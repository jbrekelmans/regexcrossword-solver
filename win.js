(function () {
    function assert(flag, message) {
        if (!flag) {
            throw new Error(message || 'assertion failed');
        }
    }

    class RegexNode {
        constructor() {
            this.parent = null;
            this.siblingIndex = -1;
            this.groupIndices = [];
        }

        // Returns the root of a new regular expression that matches the part to the right of this.
        // If this.parent is a RegexRepetitionNode then the returned regular expression will have no repetitions.
        afterThis() {
            let result = null;
            let root = this;
            if (this.parent !== null) {
                result = this.parent.cloneSubtreeWithChildrenAfter(this.siblingIndex, null);
                let node = this.parent;
                while (node.parent !== null) {
                    result = node.parent.cloneSubtreeWithChildrenAfter(node.siblingIndex - (result === null ? 0 : 1), result);
                    node = node.parent;
                }
                root = node;
            }
            console.log(`afterThis(${JSON.stringify(root.toString())}, node=${JSON.stringify(this.toString())}) => ${JSON.stringify(result === null ? '' : result.toString())}`);
            return result;
        }

        cloneSubtree() {
            return this.cloneSubtreeWithChildrenAfter(-1, null);
        }

        cloneCore(clone) {
            clone.groupIndices = this.groupIndices.slice(0);
            return clone;
        }

        getType() {
            assert(false, 'abstract method');
        }

        cloneSubtreeWithChildrenAfter(siblingIndex, insertAfter) {
            assert(false, 'abstract method');
        }
    }

    class RegexCharacterClassNode extends RegexNode {
        constructor(ranges, inverse) {
            super();
            this.ranges = ranges;
            this.inverse = inverse;
        }

        addRange(chc) {
            this.ranges.push([chc, chc]);
        }

        cloneSubtree() {
            return this.cloneCore(new RegexCharacterClassNode(this.ranges, this.inverse));
        }

        getType() {
            return 1;
        }

        setRangeMax(chc) {
            const lastRange = this.ranges[this.ranges.length - 1];
            lastRange[1] = chc;
        }

        rangesToSmt(varName) {
            var smt = '';
            assert(this.ranges.length > 0);
            if (this.inverse) {
                for (var i = 0; i < this.ranges.length; i++) {
                    var range = this.ranges[i];
                    var smtLocal = `(or (< ${varName} ${range[0]}) (> ${varName} ${range[1]}))`;
                    smt = smt.length === 0 ? smtLocal : `(and ${smt} ${smtLocal})`;
                }
            } else {
                for (var i = 0; i < this.ranges.length; i++) {
                    var range = this.ranges[i];
                    var smtLocal = `(and (>= ${varName} ${range[0]}) (<= ${varName} ${range[1]}))`;
                    smt = smt.length === 0 ? smtLocal : `(or ${smt} ${smtLocal})`;
                }
            }
            return smt;
        }

        toString() {
            let s = '[';
            if (this.inverse) {
                s += '^';
            }
            for (let i = 0; i < this.ranges.length; i++) {
                const range = this.ranges[i];
                if (range[0] === range[1]) {
                    s += '\\' + String.fromCharCode(range[0]);
                } else {
                    s += String.fromCharCode(range[0]) + '-' + String.fromCharCode(range[1]);
                }
            }
            s += ']';
            return s;
        }
    }

    class RegexLiteralNode extends RegexNode {
        constructor(chc) {
            super();
            this.chc = chc;
        }

        cloneSubtree() {
            return this.cloneCore(new RegexLiteralNode(this.chc));
        }

        getType() {
            return 2;
        }

        toString() {
            let s = String.fromCharCode(this.chc);
            if ('0'.charCodeAt(0) <= this.chc && this.chc <= '9'.charCodeAt(0)) {
                return s;
            }
            return '\\' + s;
        }
    }

    class RegexRepetitionNode extends RegexNode {
        constructor(child, min, max) {
            super();
            assert(child.parent === null);
            this.child = child;
            child.siblingIndex = 0;
            child.parent = this;
            this.min = min;
            this.max = max;
        }

        getType() {
            return 3;
        }

        cloneSubtreeWithChildrenAfter(siblingIndex, insertAfter) {
            if (siblingIndex === -1) {
                assert(insertAfter === null);
                const childClone = this.child.cloneSubtree();
                return this.cloneCore(new RegexRepetitionNode(childClone, this.min, this.max));
            }
            assert(siblingIndex === 0);
            if (insertAfter === null) {
                return null;
            }
            return this.cloneCore(new RegexRepetitionNode(insertAfter, this.min, this.max));
        }

        toString() {
            let s = this.child.toString();
            if (this.min === 0) {
                if (this.max === 1) {
                    return s + '?';
                }
                if (this.max === 1 / 0) {
                    return s + '*';
                }
            } else if (this.min === 1) {
                if (this.max === 1 / 0) {
                    return s + '+';
                }
            }
            return s + '{' + this.min + ',' + (this.max === 1 / 0 ? '' : '' + this.max) + '}';
        }
    }

    class RegexConcatenationOrAlternativesNode extends RegexNode {
        constructor(type) {
            super();
            assert(type === 4 || type === 5);
            this.type = type;
            this.children = [];
        }

        addChild(node) {
            assert(node.parent === null);
            node.siblingIndex = this.children.length;
            this.children.push(node);
            node.parent = this;
            return this;
        }

        getType() {
            return this.type;
        }

        cloneSubtreeWithChildrenAfter(siblingIndex, insertAfter) {
            assert(siblingIndex + 1 <= this.children.length);
            if (siblingIndex + 1 === this.children.length && insertAfter === null) {
                return null;
            }
            if (siblingIndex + 2 === this.children.length && insertAfter === null) {
                const clone = this.children[siblingIndex + 1].cloneSubtree();
                Array.prototype.push.apply(clone.groupIndices, this.groupIndices);
                return clone;
            }
            const clone = new RegexConcatenationOrAlternativesNode(this.type);
            if (insertAfter !== null) {
                clone.addChild(insertAfter);
            }
            for (let i = siblingIndex + 1; i < this.children.length; i++) {
                clone.addChild(this.children[i].cloneSubtree());
            }
            return this.cloneCore(clone);
        }

        toString() {
            if (this.type === 4) {
                return this.children.join('');
            }
            let s = '';
            for (let i = 0; i < this.children.length; i++) {
                const child = this.children[i];
                s = (s.length === 0 ? '(?:' : s + '|') + (child === null ? '' : child.toString());
            }
            return s + ')';
        }
    }

    class RegexBackreferenceNode extends RegexNode {
        constructor(backreference) {
            super();
            this.backreference = backreference;
        }

        cloneSubtree() {
            return new RegexBackreferenceNode(this.backreference);
        }

        getType() {
            return 6;
        }

        toString() {
            return '\\' + this.backreference;
        }
    }

    class RegexParser {
        constructor(s) {
            this.s = s;
            this.i = 0;
            this.n = this.s.length;
            this.numGroups = 0;
        }

        backslashInsideCharacterClass(node) {
            this.i++;
            assert(this.ch() !== '');
            switch (this.ch()) {
                case 's':
                    node.addRange('\t'.charCodeAt(0));
                    node.setRangeMax('\n'.charCodeAt(0));
                    node.addRange('\f'.charCodeAt(0));
                    node.setRangeMax('\r'.charCodeAt(0));
                    node.addRange(' '.charCodeAt(0));
                    break;
                case '-':
                    node.addRange(this.chc());
                    break;
                default:
                    assert(false);
            }
            this.i++;
        }

        backslashOutsideCharacterClass() {
            this.i++;
            switch (this.ch()) {
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                    assert(this.numGroups < 10);
                    const backreference = this.chc() - '0'.charCodeAt(0);
                    assert(backreference <= this.numGroups);
                    this.i++;
                    return new RegexBackreferenceNode(backreference);
                case 's':
                    {
                        const node = new RegexCharacterClassNode([], false);
                        node.addRange('\t'.charCodeAt(0));
                        node.setRangeMax('\n'.charCodeAt(0));
                        node.addRange('\f'.charCodeAt(0));
                        node.setRangeMax('\r'.charCodeAt(0));
                        node.addRange(' '.charCodeAt(0));
                        this.i++;
                        return node;
                    }
            }
            assert(false);
        }

        ch() {
            return this.s.charAt(this.i);
        }

        chc() {
            return this.s.charCodeAt(this.i);
        }

        characterClass() {
            this.i++;
            const node = new RegexCharacterClassNode([], false);
            if (this.ch() === '^') {
                node.inverse = true;
                this.i++;
            }
            while (this.ch() !== ']' && this.ch() !== '') {
                if (this.ch() === '\\') {
                    this.backslashInsideCharacterClass(node);
                    continue;
                }
                node.addRange(this.chc());
                this.i++;
                if (this.ch() === '-') {
                    this.i++;
                    if (this.ch() === '') {
                        break;
                    }
                    if (this.ch() === ']') {
                        node.addRange('-'.charCodeAt(0));
                        break;
                    }
                    if (this.ch() === '\\') {
                        node.addRange('-'.charCodeAt(0));
                        this.backslashInsideCharacterClass(node);
                        continue;
                    }
                    node.setRangeMax(this.chc());
                    this.i++;
                }
            }
            assert(this.ch() !== '');
            this.i++;
            return this.repetitionOptional(node);
        }

        dot() {
            this.i++;
            const chc = '\n'.charCodeAt(0);
            return this.repetitionOptional(new RegexCharacterClassNode([[chc, chc]], true));
        }

        group() {
            this.i++;
            assert(this.ch() !== '?');
            const node = this.node(true);
            assert(this.ch() === ')');
            this.i++;
            this.numGroups++;
            node.groupIndices.push(this.numGroups);
            return this.repetitionOptional(node);
        }

        literal() {
            const node = new RegexLiteralNode(this.chc());
            this.i++;
            return this.repetitionOptional(node);
        }

        node(stopOnRightParenthesis) {
            let node3 = null;
            do {
                let node1 = null;
                outer: while (this.i < this.n) {
                    let node2;
                    switch (this.ch()) {
                        case ')':
                            if (stopOnRightParenthesis) {
                                break outer;
                            }
                            node2 = this.literal();
                            break;
                        case '[':
                            node2 = this.characterClass();
                            break;
                        case '(':
                            node2 = this.group();
                            break;
                        case '|':
                            break outer;
                        case '\\':
                            node2 = this.backslashOutsideCharacterClass();
                            break;
                        case '.':
                            node2 = this.dot();
                            break;
                        default:
                            node2 = this.literal();
                            break;
                    }
                    if (node1 === null) {
                        node1 = node2;
                    } else {
                        if (node1.type !== 4) {
                            node1 = new RegexConcatenationOrAlternativesNode(4).addChild(node1);
                        }
                        node1.addChild(node2);
                    }
                }
                if (node3 === null) {
                    node3 = node1;
                } else {
                    if (node3.type !== 5) {
                        node3 = new RegexConcatenationOrAlternativesNode(5).addChild(node3);
                    }
                    node3.addChild(node1);
                }
                if (this.ch() !== '|') {
                    assert(!stopOnRightParenthesis || this.i < this.n);
                    return node3;
                }
                this.i++;
            } while (true);
        }

        repetitionOptional(node) {
            let min, max;
            switch (this.ch()) {
                case '?':
                    min = 0;
                    max = 1;
                    break;
                case '+':
                    min = 1;
                    max = 1 / 0;
                    break;
                case '*':
                    min = 0;
                    max = 1 / 0;
                    break;
                case '{':
                    min = 0;
                    max = 1 / 0;
                    this.i++;
                    if (/[0-9]/.test(this.ch())) {
                        min = 0;
                        do {
                            min = min * 10 + this.chc() - '0'.charCodeAt(0);
                            this.i++;
                        } while (/[0-9]/.test(this.ch()));
                        if (this.ch() === '}') {
                            max = min;
                            break;
                        }
                    }
                    if (this.ch() === ',') {
                        this.i++;
                        if (this.ch() === '}') {
                            break;
                        }
                    }
                    assert(false);
                    break;
                default:
                    return node;
            }
            this.i++;
            assert(!(node instanceof RegexRepetitionNode));
            return new RegexRepetitionNode(node, min, max);
        }

        run() {
            let gotError = true;
            try {
                const node = this.node(false);
                assert(this.i === this.n);
                gotError = false;
                return node;
            } finally {
                if (gotError) {
                    console.log(`error parsing regex ${JSON.stringify(this.s)}, remainder of input: ${JSON.stringify(this.s.substring(this.i))}`);
                }
            }
        }
    }

    function parseRegex(s) {
        return new RegexParser(s).run();
    }

    class RegexToFormulaConverter {
        constructor(regex, colCount, row, transposed, getSmtVarNameFunction) {
            this.getSmtVarNameFunction = getSmtVarNameFunction;
            this.colCount = colCount;
            this.row = row;
            this.transposed = transposed;
            this.currentFork = null;
            this.currentForkUnexpectedEOS = false;
            this.forks = [
                {
                    col: 0,
                    regex,
                    groupFirstCaptures: [],
                    smt: '',
                }
            ];
            this.smt = '';
        }

        currentForkAddSmt(smt) {
            this.currentFork.smt = this.currentFork.smt === '' ? smt : `(and ${this.currentFork.smt} ${smt})`;
            this.currentFork.col++;
        }

        currentForkGetSmtVarName(col) {
            if (col === undefined) {
                col = this.currentFork.col;
            }
            if (this.transposed) {
                return this.getSmtVarNameFunction(this.row, col);
            }
            return this.getSmtVarNameFunction(col, this.row);
        }

        currentForkIsEndOfString() {
            return this.currentFork.col === this.colCount;
        }

        runFork() {
            this.currentFork = this.forks.pop();
            if (this.currentFork.regex === null) {
                return;
            }
            this.currentForkUnexpectedEOS = false;
            console.log(`running fork: ${this.currentFork.regex.toString()}`);
            this.runForkRecursive(this.currentFork.regex);
            if (!this.currentForkUnexpectedEOS && this.currentFork.col === this.colCount) {
                this.smt = this.smt.length === 0 ? this.currentFork.smt : `(or ${this.smt} ${this.currentFork.smt})`;
            }
        }

        runForkRecursive(regexNode) {
            for (let i = 0; i < regexNode.groupIndices.length; i++) {
                const captureStartIndex = regexNode.groupIndices[i] * 2;
                if (this.currentFork.groupFirstCaptures[captureStartIndex] === undefined) {
                    this.currentFork.groupFirstCaptures[captureStartIndex] = this.currentFork.col;
                }
            }
            let flag = true;
            switch (regexNode.getType()) {
                case 1:
                    // character class
                    if (this.currentForkIsEndOfString()) {
                        this.currentForkUnexpectedEOS = true;
                        return false;
                    }
                    this.currentForkAddSmt(regexNode.rangesToSmt(this.currentForkGetSmtVarName()));
                    break;
                case 2:
                    // literal node
                    if (this.currentForkIsEndOfString()) {
                        this.currentForkUnexpectedEOS = true;
                        return false;
                    }
                    this.currentForkAddSmt(`(= ${this.currentForkGetSmtVarName()} ${regexNode.chc})`);
                    break;
                case 3:
                    flag = this.runForkRecursiveRepetition(regexNode);
                    break;
                case 4:
                    flag = this.runForkRecursiveConcatenation(regexNode);
                    break;
                case 5:
                    flag = this.runForkRecursiveAlternatives(regexNode);
                    break;
                case 6:
                    flag = this.runForkRecursiveBackreference(regexNode);
                    break;
                default:
                    assert(false);
                    break;
            }
            if (!flag) {
                return false;
            }
            for (let i = 0; i < regexNode.groupIndices.length; i++) {
                const captureEndIndex = regexNode.groupIndices[i] * 2 + 1;
                if (this.currentFork.groupFirstCaptures[captureEndIndex] === undefined) {
                    this.currentFork.groupFirstCaptures[captureEndIndex] = this.currentFork.col;
                }
            }
            return true;
        }

        runForkRecursiveAlternatives(regexNode) {
            // create a fork for each alternative...
            const children = regexNode.children;
            let i = children.length;
            while (i > 0 && children[i - 1] === null) {
                i--;
            }
            if (i === 0) {
                return true;
            }
            for (let j = 0; j < i - 1; j++) {
                if (children[j] === null) {
                    continue;
                }
                // Fork here, with alternative j
                const regexNodeAfterThis = regexNode.afterThis();
                let regexNodeFork = children[j].cloneSubtree();
                if (regexNodeAfterThis !== null) {
                    regexNodeFork = new RegexConcatenationOrAlternativesNode(4).addChild(regexNodeFork).addChild(regexNodeAfterThis);
                }
                this.forks.push({
                    col: this.currentFork.col,
                    groupFirstCaptures: this.currentFork.groupFirstCaptures.slice(0),
                    regex: regexNodeFork,
                    smt: this.currentFork.smt,
                });
            }
            // i is the index of a non-null alternative...
            return this.runForkRecursive(children[i - 1]);
        }

        runForkRecursiveBackreference(regexNode) {
            const index = regexNode.backreference * 2;
            assert(index + 1 < this.currentFork.groupFirstCaptures.length);
            const colStart = this.currentFork.groupFirstCaptures[index];
            const colEnd = this.currentFork.groupFirstCaptures[index + 1];
            if ((this.colcount - this.currentFork.col) < (colEnd - colStart)) {
                // Remaining characters is smaller than length of first capture of group that was backreferenced. 
                this.currentForkUnexpectedEOS = true;
                return false;
            }
            for (let col = colStart; col < colEnd; col++) {
                const varName1 = this.currentForkGetSmtVarName(col);
                const varName2 = this.currentForkGetSmtVarName();
                this.currentForkAddSmt(`(= ${varName2} ${varName1})`);
            }
            return true;
        }

        runForkRecursiveConcatenation(regexNode) {
            for (let i = 0; i < regexNode.children.length; i++) {
                if (!this.runForkRecursive(regexNode.children[i])) {
                    return false;
                }
            }
            return true;
        }

        runForkRecursiveRepetition(regexNode1) {
            let i = 0;
            while (i < regexNode1.min) {
                if (!this.runForkRecursive(regexNode1.child)) {
                    return false;
                }
                i++;
            }
            let regexNode2 = null;
            while (true) {
                if (i === regexNode1.max || this.currentForkIsEndOfString()) {
                    break;
                }
                const smt = this.currentFork.smt;
                const groupFirstCaptures = this.currentFork.groupFirstCaptures.slice(0);
                const col = this.currentFork.col;
                if (!this.runForkRecursive(regexNode1.child)) {
                    break;
                }
                if (regexNode2 === null) {
                    regexNode2 = regexNode1.afterThis();
                }
                // Create a fork that has exactly i repetitions.
                this.forks.push({
                    col,
                    groupFirstCaptures,
                    regex: regexNode2,
                    smt,
                });
                i++;
            }
            return true;
        }

        run() {
            while (this.forks.length > 0) {
                this.runFork();
            }
            assert(this.smt.length > 0);
            return this.smt;
        }
    }

    function clues(e) {
        return Array.prototype.slice.call(e.querySelectorAll(".clue"), 0);
    }

    function getSmtVarNameFunction(rowCount) {
        return (col, row) => 'x' + (col * rowCount + row + 1);
    }

    function main() {
        let colsRaw;
        let rowsRaw;
        const table = document.querySelectorAll("div.grid table")[0];
        const colsRaw1 = clues(table.tHead).map(c => c.innerText);
        rowsRaw = Array.prototype.map.call(table.tBodies[0].rows, row => clues(row).map(c => c.innerText).filter(s => s.length > 0));
        const colsRaw2 = clues(table.tFoot).map(c => c.innerText);
        colsRaw = colsRaw1.map((s, i) => colsRaw2[i].length > 0 ? [s, colsRaw2[i]] : [s]);
        console.log('colsRaw = ', JSON.stringify(colsRaw), ';');
        console.log('rowsRaw = ', JSON.stringify(rowsRaw), ';');
        // colsRaw = [["[^SPEAK]+"], ["EP|IP|EF"]];
        // rowsRaw = [["HE|LL|O+"], ["[PLEASE]+"]];

        // colsRaw = [["[^RO\\sE]*(WHE|WHO)", "[^VYS]+"], ["[ARE](.)[SAINT]+\\1V", ".(\\sSAI).*"], [".{2}[ST\\sEL]+", "(LE|\\sT|S|OR)+"]];
        // rowsRaw = [
        //     ["(RR|FRO)*", "[FR\\sO]+"],
        //     ["[^SAINT]+", "(M\\s|SM)[ROSE]"],
        //     ["[\\sUSH]*", "(S|US)+"], ["[A\\sI]+", "[^AW]A.*"], ["[WITH]*", "[^HEAR]+"], ["[HEL\\s]+", ".*[FIL]"], [".*", "(VE|O|VO)+"]];

        const cols = colsRaw.map(sList => sList.map(parseRegex));
        const rows = rowsRaw.map(sList => sList.map(parseRegex));

        const getSmtVarName = getSmtVarNameFunction(rowsRaw.length);
        let smt = '';
        for (let col = 0; col < cols.length; col++) {
            for (let row = 0; row < rows.length; row++) {
                smt += `(declare-const ${getSmtVarName(col, row)} Int)\n`;
            }
        }
        for (let row = 0; row < rows.length; row++) {
            const regexList = rows[row];
            smt += `(assert ${new RegexToFormulaConverter(regexList[0], cols.length, row, false, getSmtVarName).run()})\n`;
            if (regexList.length > 1) {
                smt += `(assert ${new RegexToFormulaConverter(regexList[1], cols.length, row, false, getSmtVarName).run()})\n`;
            }
        }
        for (let col = 0; col < cols.length; col++) {
            const regexList = cols[col];
            smt += `(assert ${new RegexToFormulaConverter(regexList[0], rows.length, col, true, getSmtVarName).run()})\n`;
            if (regexList.length > 1) {
                smt += `(assert ${new RegexToFormulaConverter(regexList[1], rows.length, col, true, getSmtVarName).run()})\n`;
            }
        }
        smt += `(check-sat)\n(get-model)\n`;
        console.log(smt);


        (typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : null).setResult = function (s) {
            let i = 0;
            let levelStarts = [];
            while (i < s.length) {
                switch (s.charAt(i)) {
                    case '(':
                        levelStarts.push(i);
                        break;
                    case ')':
                        const start = levelStarts.pop();
                        if (levelStarts.length === 1) {
                            const parts = s.substring(start + 1, i).split(/\s+/g);
                            const name = Number(name.substring(1));
                            const value = parts[4];
                            console.log(name, value);
                            'x' + (col * rowCount + row + 1);

                        }
                        break;
                }
                i++;
            }
        };
    }

    main();
})();