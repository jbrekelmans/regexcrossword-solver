# Introduction
This repository contains a script that allows mechanical solving of puzzles from regexcrossword.com.
## How to use it
1. Open the regular expression crossword puzzle in Chrome, [such as this one](https://regexcrossword.com/challenges/beginner/puzzles/1).
1. Open Chrome developer tools for the tab of step 1.
1. Copy the contents of [win.js](win.js) into the clipboard.
1. In the Chrome developer tools Console, paste the script and press enter.
1. Copy the output to the clipboard. It should look like this:
    ```
    (declare-const x1 Int)
    (declare-const x2 Int)
    (declare-const x3 Int)
    (declare-const x4 Int)
    (assert (or (or (and (= x1 79) (= x3 79)) (and (= x1 76) (= x3 76))) (and (= x1 72) (= x3 69))))
    (assert (and (or (or (or (or (or (and (>= x2 80) (<= x2 80)) (and (>= x2 76) (<= x2 76))) (and (>= x2 69) (<= x2 69))) (and (>= x2 65) (<= x2 65))) (and (>= x2 83) (<= x2 83))) (and (>= x2 69) (<= x2 69))) (or (or (or (or (or (and (>= x4 80) (<= x4 80)) (and (>= x4 76) (<= x4 76))) (and (>= x4 69) (<= x4 69))) (and (>= x4 65) (<= x4 65))) (and (>= x4 83) (<= x4 83))) (and (>= x4 69) (<= x4 69)))))
    (assert (and (and (and (and (and (or (< x1 83) (> x1 83)) (or (< x1 80) (> x1 80))) (or (< x1 69) (> x1 69))) (or (< x1 65) (> x1 65))) (or (< x1 75) (> x1 75))) (and (and (and (and (or (< x2 83) (> x2 83)) (or (< x2 80) (> x2 80))) (or (< x2 69) (> x2 69))) (or (< x2 65) (> x2 65))) (or (< x2 75) (> x2 75)))))
    (assert (or (or (and (= x3 69) (= x4 70)) (and (= x3 73) (= x4 80))) (and (= x3 69) (= x4 80))))
    (check-sat)
    (get-model)
    ```
1. Open https://rise4fun.com/Z3.
1. Paste the SMT formula copied in step 5 and evaluate it.
