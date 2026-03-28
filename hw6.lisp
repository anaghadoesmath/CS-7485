#|

 Copyright © 2026 by Pete Manolios and Andrew Walter
 CS 4820 Spring 2026

 Homework 6
 Due: 3/28 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 6".

 The group members are:

Anagha ... (put the names of the group members here)

|#

#|

 In this homework, you will learn how to use Z3, a modern
 SMT (satisfiability modulo theories) solver from inside of
 ACL2s. Andrew has developed API bindings that provide a (property
 ...)-like interface to Z3. There are Z3 bindings for most languages,
 including Python, OCaml, Haskell, etc.

 You'll develop a simple Sudoku solver using the Z3 bindings. You will
 also explore different ways of encoding problems and how that affects
 performance.

 SMT solvers combine SAT solvers with solvers for additional
 theories (for example, the theory of uninterpreted functions, or real
 arithmetic with addition and multiplication). In this way, SMT
 solvers can check the satisfiability of expressions that contain
 variables and functions from several different theories at once.

 Consider the following example:
 Let x and y be two strings. Is the following satisfiable?
 (^ (< (length x) 3)
    (< (length y) 3)
    (> (length (string-append x y)) 6))
 It is not - the length of (string-append x y) is at most (length x) + (length y).

 We can state this as an ACL2s property:
 (property (x :string y :string)
           (=> (^ (< (length x) 3)
                  (< (length y) 3))
               (not (> (length (string-append x y)) 6))))
 
 For an SMT solver to be able to report that this statement is UNSAT,
 it needs to understand how length and string-append relate to each
 other. If we ask our DP implementation from Homework 4 whether the
 propositional skeleton is satisfiable, it will report that it is SAT
 because it doesn't reason about length, <, >, string-append, etc.

 As you'll learn, we can ask Z3 to check the satisfiability of this
 statement using the following query (after setting up dependencies):

 (z3-assert (x :string y :string)
            (and (< (str.len x) 3)
                 (< (str.len y) 3)
                 (> (str.len (str.++ x y)) 6)))
 (check-sat)

 Z3 reports :UNSAT.

 Let's get started by first going through some setup instructions for
 the Z3-Lisp API.
|#

#|
=====================================
=            Z3 Setup               =
=====================================

You first need to install Z3 onto your system. Many package managers
offer a prepackaged version of Z3, so it is likely easiest to install
Z3 using your package manager rather than building it from source. If
you're on macOS, Homebrew provides prebuilt Z3 packages as well.

If using Windows Subsystem for Linux to run ACL2s, you should install
Z3 into WSL rather than in "regular" Windows.

Depending on your operating system, you may also need to install
a "z3-dev" package. On Ubuntu, this package is called `libz3-dev`.

You will also need a working C compiler to use the interface. On
Ubuntu, the `build-essential` package should include everything you
need, though it is fairly large and contains some unneeded
software. One could also try just installing `gcc` or `clang`.

After getting Z3 installed, you should be able to run it through the
command line. To test this, execute `z3 --version` in your terminal
and verify that it reports something along the lines of `Z3 version
4.15.4 - 64 bit` (your version or architecture may be different,
that's OK).

To install the z3 bindings, follow the instructions at
https://github.com/mister-walter/cl-z3.  If you run into any issues,
ask questions on Piazza.

|#

;; Exit out of ACL2s into raw Lisp
:q

(load "~/quicklisp/setup.lisp")
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :hwk6
  (:use :cl :z3))
(in-package :hwk6)

;; Before we do anything, we must start Z3.
(solver-init)

;; ===========================
;;           Basics
;; ===========================
;; To use Z3, one adds one or more assertions to Z3 and then uses
;; (check-sat) to ask Z3 to perform a satisfiability check.
;; Let's try something simple first.
;; We want to know if the formula `x ^ y` is satisfiable. Let's add it
;; to Z3's stack:
(z3-assert (x :bool y :bool)
           (and x y))
;; We can see the contents of the solver using print-solver.
;;(print-solver)

;; Now, we can ask Z3 to check satisfiability:
(check-sat)
(get-model-as-assignment)
;; We get an assignment: ((X T) (Y T)). This indicates that the set of
;; assertions we've added to Z3's stack is satisfiable, and provides a
;; satisfying assignment.

;; Note that Z3 still contains the stack of assertions; if we call
;; check-sat again, we'll get another satisfying assignment.
(check-sat)
(get-model-as-assignment)
;; In this case the satisfying assignment is the same (since there is
;; only one distinct satisfying assignment for the formula `x ^ y`),
;; but in general the assignment may be different.

;; To clear the set of assignments, we can use `(solver-reset)`.
(solver-reset)

;; =========================
;;    The Assertion Stack
;; =========================
;; Sometimes, it may be useful to be able to remove just a subset of
;; assertions instead of resetting all of them. Z3 supports this with
;; the concept of scopes.
;; When a scope `S` is created, Z3 saves the set of assertions that
;; exist at that time. When `S` is popped, Z3 will return its set of
;; assertions to its state at the time `S` was created.

;; Let's see an example.

;; Create an initial scope that we can return to when we want an empty
;; set of assertions
(solver-push)

(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; This is SAT.
(check-sat)
(get-model-as-assignment)

;; There is currently 1 assertion.
(print-solver)

;; Let's create another scope, one that contains the above assertion.
(solver-push)

;; We'll add an assertion that forces x to be false.
(z3-assert (x :bool)
           (not x))

;; Now the set of assertions is UNSAT!
(check-sat)

;; There are now 2 assertions.
(print-solver)

;; Let's pop off the top scope. This will remove the assertion we just
;; added.
(solver-pop)

;; As expected, check-sat returns a satisfying assignment again.
(check-sat)
(get-model-as-assignment)

;; We're back to the same set of assertions that we had when we ran
;; (solver-push) the second time.
(print-solver)

;; We can pop back to the empty set of assertions that we had after we
;; reset the solver.
(solver-pop)
(print-solver)

;; ==================
;;       Sorts
;; ==================
;; Z3 supports many variable types, which it calls "sorts".
;; We've already seen booleans and integers.
(solver-push)
(z3-assert (x :bool y :int z :string)
           (and x (> y 5) (= (str.len z) 3)))
(check-sat)
(get-model-as-assignment)

;; Z3 also supports sequence types, including strings.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y :string)
           (and (> (seq.len x) 3)
                (> (str.len y) 3)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; Here's another example showing more of the sequence operators.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y (:seq :int) z (:seq :int))
           (and (> (seq.len x) 3)
                (> (seq.len y) 1)
                ;; x contains the subsequence consisting of the 0th element of y
                ;; this is equivalent to saying that x contains the 0th element of y
                (seq.contains x (seq.at y 0))
                ;; z equals the concatenation of x and y
                (= z (seq.++ x y))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; You can define enumeration sorts as follows:
(register-enum-sort :my-sort (a b c))
;; this sort consists of one of the three values a, b, and c.

;; Now you can use this sort in assertions!
(solver-push)
(z3-assert (x :my-sort y :my-sort)
           (and (not (= x y))
                ;; To represent an element of an enum, you need to use
                ;; `enumval` as shown here.
                (not (= x (enumval :my-sort a)))
                (not (= y (enumval :my-sort b)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

#|
 Note that operations that may cause exceptions in other languages
 (like division by zero) are underspecified in Z3. This means that Z3
 treats `(/ x 0)` as an uninterpreted function that it may assign any
 value to. This can lead to unexpected behavior if you're not careful.

 For example, Z3 reports that the following is satisfiable, since it
 can assign `x` and `y` different values, and has the flexibility to
 have division by 0 for the value of `x` return 3, and division by 0
 for the value of `y` return 4.
|#
(solver-push)
(z3-assert (x :int y :int)
           (and (= (/ x 0) 3)
                (= (/ y 0) 4)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; There are many more operators and a few more sorts supported by Z3
;; and the lisp-z3 interface. See the operators.md file in
;; <ql-local-projects>/lisp-z3 for more information. The operator
;; documentation is also available on the course website (right next
;; to the HWK 6 link). Feel free to ask on Piazza if anything is
;; unclear.

;; One final note: sometimes, `check-sat` may not return an assignment
;; for some of the input variables provided to `z3-assert`. This often
;; is because Z3 is able to determine that the value of those
;; variables does not affect the satisfiability of the set of
;; assertions being checked, so it returns a partial assignment. If
;; you get a partial assignment, then all possible ways of extending
;; the partial assignment to total assignments are also assignments.

(solver-reset)

;; ==========================
;;            Q1
;; ==========================
;; 15 pts (3 pts each)
;;
;; For each of the following statements, encode the statement into a
;; SMT problem that Z3 can handle using `z3-assert` and report whether
;; the statement is satisfiable or not.
;;
;; As noted above, the list of operators supported by the Lisp-Z3
;; interface is available in HTML format on the course website <link>,
;; as well as in Markdown format in
;; <ql-local-projects>/lisp-z3/operators.md.

;; 1a:
;; x, y, and z are boolean variables.
;; if x is true, then both y and z are true.
;; if y is true, then x is not true and z is not true.
;; if z is false, then y is false

(solver-push)
(z3-assert (x y z :bool)
	   (and (=> x (and y z))
		(=> y (and (not x) (not z)))
		(=> (not z) (not y))))
(check-sat)
(solver-pop)

;; 1b:
;; x,y,z,p and q are all string variables.
;; the concatenation of x y and z is equal to the concatenation of p and q
;; all of the strings have at least length 2
;; y starts with "ab"
;; p ends with "ba"

(solver-push)
(z3-assert (x y z p q :string)
	   (and (= (str.++ (str.++ x y) z)(str.++ p q))
		(>= (str.len x) 2)
		(>= (str.len y) 2)
		(>= (str.len z) 2)
		(>= (str.len p) 2)
		(>= (str.len q) 2)
		(str.prefixof "ab" y)
		(= (seq.extract p (- (str.len p) 2) 2) "ba")))
(check-sat)
(solver-pop)


;; 1c:
;; x is a sequence of booleans
;; y is an integer variable
;; y is between 0 and 32 inclusive
;; x has length equal to y
;; if x has at least one element and the first element of x is true,
;; then the length of x is even. Otherwise, the length of x is odd.

(solver-push)
(z3-assert (x (:seq :bool) y :int)
	   (and (>= y 0)
		(<= y 32)
		(= (seq.len x) y)
		(ite (and (> y 0) (seq.nth x 0))
		     (= (mod y 2) 0)
		     (= (mod y 2) 1))))
(check-sat)
;;filters the output of the auxiliary function
(let ((m (get-model-as-assignment)))
  (remove-if-not (lambda (kv) (member (car kv) '(X Y))) m))
(solver-pop)



;; Now, we'll have some fun by encoding logic puzzles as SMT problems.

;; 1d:
;; (adapted from "What is the Name of This Book?" by Raymond Smullyan)

;; An island is inhabited by "knights" who always tell the truth, and
;; "knaves" who always lie. A stranger comes across three inhabitants
;; of this island standing together (Alice, Bob, and Clara) and asks
;; Alice "How many knights are among you?". Alice answers
;; indistinctly, and the stranger then asks Bob what Alice said. Bob
;; responds "Alice said there is one knight among us." Clara
;; interjects, saying "Don't believe Bob, he's lying!"
;; Is Bob a knight or a knave? Is Clara a knight or a knave?

(solver-push)
;;A-Alice; knight-count- #of knights; B-Bob; C-Clara; said-count; knight-sat;
(z3-assert (a b c :bool
           said-count knight-count :int)
           (and (>= said-count 0)
                (<= said-count 3)
                (= knight-count (+ (ite a 1 0)
                                   (ite b 1 0)
                                   (ite c 1 0)))
                (= a (= said-count knight-count))
                (= b (= said-count 1))
                (= c (not (= said-count 1)))))
(check-sat)
(let ((m (get-model-as-assignment)))
  (list (list 'alice (cadr (assoc 'a m :test #'equal)))
        (list 'bob   (cadr (assoc 'b m :test #'equal)))
        (list 'clara (cadr (assoc 'c m :test #'equal)))))
(solver-pop)


;; 1e:
;; (adapted from from "My best puzzles in logic and reasoning" by
;; Hubert Phillips, now public domain)
#|
Mr. Fireman, Mr. Guard, and Mr. Driver are (not necessarily
respectively) the fireman, guard, and driver of an express
train. Exactly one of the following statements is true:
- Mr. Driver is not the guard
- Mr. Fireman is not the driver
- Mr. Driver is the driver
- Mr. Fireman is not the guard

Is the above set of constraints consistent? If so, who has what job?

(hint: an enumeration sort might be helpful here)
|#

(solver-push)
(register-enum-sort :train-job (fireman-job guard-job driver-job))
(z3-assert (mr-fireman mr-guard mr-driver :train-job
           s1 s2 s3 s4 :bool)
           (and (distinct mr-fireman mr-guard mr-driver)
                (= s1 (not (= mr-driver (enumval :train-job guard-job))))
                (= s2 (not (= mr-fireman (enumval :train-job driver-job))))
                (= s3 (= mr-driver (enumval :train-job driver-job)))
                (= s4 (not (= mr-fireman (enumval :train-job guard-job))))
                (or s1 s2 s3 s4)
                (not (and s1 s2))
                (not (and s1 s3))
                (not (and s1 s4))
                (not (and s2 s3))
                (not (and s2 s4))
                (not (and s3 s4))))
(check-sat)
(let ((m (get-model-as-assignment)))
  (mapcar (lambda (v) (assoc v m :test #'equal))
          '(mr-fireman mr-guard mr-driver)))
(solver-pop)


;; ===========================
;;    Generating Constraints
;; ===========================
;;
;; It can get tedious to manually generate the constraints that encode
;; a particular problem. Since constraints are written using
;; S-expressions, we can use Lisp to generate constraints
;; programmatically.

;; Let's take a look at a very simple problem: we want to use Z3 to
;; find a normal semimagic square of order 3. A non-trivial semimagic
;; square of order `n` is an `n` x `n` grid of integers between 1 and
;; n^2 inclusive such that all of the rows and columns sum to the same
;; value. Since we did not specify that the magic square is
;; non-trivial, more than one cell in the square may have the same
;; value.

;; First, let's think about the constraints that we will need to
;; generate for this problem. We will likely want to encode each
;; square in the grid as an integer variable, and then add constraints
;; that state that the sums of the integer variables for each row and
;; column all equal the same value.

;; Let's consider an order-2 semimagic square. For this square, we
;; need 4 integer variables. I'll call them X0, X1, X2, and X3. They
;; need to have values between 1 and 4 inclusive, e.g. the following
;; conjunction must hold:
#|
(and (> X0 0) (<= X0 4)
     (> X1 0) (<= X1 4)
     (> X2 0) (<= X2 4)
     (> X3 0) (<= X3 4))
|#

;; Our square will look like this:
#|
+---------+
| X0 | X1 |
+---------+
| X2 | X3 |
+---------+
|#
;; Now, we need to encode that the sums of the rows and columns are
;; the same. I'll introduce another integer variable, S, to represent
;; the sum of the rows and columns.
;; The constraints are:
;; (= (+ X0 X1) S) ;; row 0
;; (= (+ X2 X3) S) ;; row 1
;; (= (+ X0 X2) S) ;; col 0
;; (= (+ X1 X3) S) ;; col 1

;; To write this in a form that `z3-assert` can understand, we need to
;; take the conjunction of the row and column constraints, and
;; generate a list defining each variable and its sort. We also need
;; to add in the constraints on the range of each variable.
;; In this case, we would generate:

(z3-assert (X0 :int X1 :int X2 :int X3 :int S :int)
           (and (> X0 0) (<= X0 4) ;; x0 is within the appropriate range
                (> X1 0) (<= X1 4) ;; ditto for x1
                (> X2 0) (<= X2 4)
                (> X3 0) (<= X3 4)
                (= (+ X0 X1) S) ;; row 0
                (= (+ X2 X3) S) ;; row 1
                (= (+ X0 X2) S) ;; col 0
                (= (+ X1 X3) S))) ;; col 1
;; We can use Z3 to determine if any such magic square exists:
(check-sat)
;; Indeed, one exists: all of the squares are 1. Boring, but it works.
(solver-reset)

;; Now, let's generate those constraints for an order-3 semimagic
;; square programmatically.

;; When dealing with a grid of variables, it is often useful to have a
;; way of transforming a pair of a row and column indices into the
;; variable at that location. I'll define such a function below.
(defun get-3x3-magic-square-var (row col)
  ;; See the Common Lisp HyperSpec for more information about any
  ;; Common Lisp function.
  ;; For example, the documentation for `concatenate` can be found at
  ;; http://clhs.lisp.se/Body/f_concat.htm
  ;; You can also ask SBCL for documentation for a function
  ;; by running (describe #'<function-name>) in the REPL.
  ;; e.g. (describe #'concatenate)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 3))))))
;;

;; This should give us the variable for the first cell, X0
(get-3x3-magic-square-var 0 0)
;; Don't worry if it prints out :INTERNAL afterwards - `intern`
;; actually returns multiple values (see the HyperSpec for more info)

;; Now, let's define a function that will generate the constraint that
;; states that the sum of a particular row should be equal to some variable.
(defun 3x3-magic-square-row-sum (row sum-var)
  ;; I'm going to use the loop macro here. This is a very powerful
  ;; macro that allows us to avoid writing helper functions just to
  ;; perform basic loops.
  ;; See the HyperSpec and
  ;; https://gigamonkeys.com/book/loop-for-black-belts.html for more
  ;; information.
  ;; We want to first generate the variables corresponding to each
  ;; cell in this row.
  (let ((row-squares
         (loop for col below 3
               collect (get-3x3-magic-square-var row col))))
    ;; Then, we want to say that the sum of the squares is equal to
    ;; whatever the sum-var is.
    `(= ,sum-var (+ . ,row-squares))))

;; Just as a sanity check, let's generate the constraint for the first row.
(3x3-magic-square-row-sum 0 'S)
;; great, exactly as we expected.

;; Now, let's define a similar function for columns.
(defun 3x3-magic-square-col-sum (col sum-var)
  (let ((col-squares
         (loop for row below 3
               collect (get-3x3-magic-square-var row col))))
    `(= ,sum-var (+ . ,col-squares))))
;; Another sanity check...
(3x3-magic-square-col-sum 0 'S)
;; looks good.

;; Now, let's put it all together. We want to generate the constraints
;; for all of the rows and all of the columns and take the conjunction
;; of them.
(defun 3x3-magic-square-row-col-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var))))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints)))
;; Great, this is a conjunction of equalities, which is what we expect.
(3x3-magic-square-row-col-constraints 'S)

;; Finally, we need to generate the list of variables and their sorts.
(defun 3x3-magic-square-var-specs (sum-var)
  (let ((cell-vars (loop for row below 3 append
                         (loop for col below 3 append
                               `(,(get-3x3-magic-square-var row col) :int)))))
    `(,sum-var :int ,@cell-vars)))

(3x3-magic-square-var-specs 'S)

;; We also need to assert that all of the values are between 1 and 9.
(defun 3x3-magic-square-vars-between-1-and-9 ()
  (cons 'and (loop for row below 3 append
                   (loop for col below 3 append
                         `((>= ,(get-3x3-magic-square-var row col) 1)
                           (<= ,(get-3x3-magic-square-var row col) 9))))))

;; Now, we just need to pass this information into `z3-assert`.
;; `z3-assert` is just a macro that calls `z3-assert-fn` on its quoted
;; input. All this means is that we can skip some shenanigans with
;; backquote and just pass the constraints and variable specifications
;; directly into `z3-assert-fn`.

(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(check-sat)
;; We get our satisfying assignment, still boring (all 1s) but correct.
(solver-pop)

;; You'll expand upon this in Q2 below.

(solver-reset)

;; ==========================
;;            Q2
;; ==========================
;; 25 pts

;; Use Z3 to find a normal non-trivial magic square of order 3.

;; You should use a similar approach to that shown above to
;; programmatically generate the constraints and pass them into
;; `z3-assert-fn`.

;; A magic square is a semimagic square that also satisfies the
;; property that all diagonals also sum to the same value as all of
;; the rows and columns.
;; A non-trivial magic square is a magic square such that no two cells
;; have the same value.

;;diagonal constraints
(defun 3x3-magic-square-diagonal-constraints (sum-var)
  `(and (= ,sum-var (+ ,(get-3x3-magic-square-var 0 0)
                       ,(get-3x3-magic-square-var 1 1)
                       ,(get-3x3-magic-square-var 2 2)))
        (= ,sum-var (+ ,(get-3x3-magic-square-var 0 2)
                       ,(get-3x3-magic-square-var 1 1)
                       ,(get-3x3-magic-square-var 2 0)))))

;distinct constraint
(defun 3x3-magic-square-distinct-constraint ()
  (let ((cells (loop for row below 3 append
                     (loop for col below 3 collect
                           (get-3x3-magic-square-var row col)))))
    `(distinct ,@cells)))

;pretty-print the solution
(defun print-3x3-magic-square-solution (soln)
  (format t "~%Q2 Magic Square (sum S = ~A):~%" (cadr (assoc 'S soln)))
  (loop for row below 3
        do (progn
             (loop for col below 3
                   for var = (get-3x3-magic-square-var row col)
                   for val = (cadr (assoc var soln))
                   do (format t "~2A " val))
             (terpri))))


(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-diagonal-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-distinct-constraint))
;if sat, prints the magic square; can use this instead of check-sat and get-model-as-assignment
(let ((q2-result (check-sat)))
  (if (equal q2-result :sat)
      (let ((q2-model (get-model-as-assignment)))
        (print-3x3-magic-square-solution q2-model)
        q2-model)
      q2-result))
;;(check-sat)
;;(get-model-as-assignment)
(solver-pop)

;; ==========================
;;            Q3
;; ==========================
;; 30 pts
;;
;; Develop a Sudoku solver that uses an approach similar to that
;; described above to use Z3 to generate solutions to a given starting
;; board. The top-level function should be called `solve-sudoku`, and
;; should take a starting board as an argument. The format of the
;; starting board will be defined below. `solve-sudoku` should return
;; either 'UNSAT (if no valid Sudoku board also satisfies the starting
;; board) or an assignment (a list of 2-element lists, similar to a
;; let binding, where the first element is the variable name and the
;; second is the assignment) that represents a filled-in Sudoku board
;; that satisfies the starting board's assignments.
;;
;; A valid Sudoku board is a 3x3 grid of 3x3 boxes. The 9 cells in
;; each box must all be integers from 1 to 9 inclusive, and must all
;; be different. Every row and column of the 9x9 Sudoku grid must
;; contain every integer from 1 to 9 inclusive exactly once.
;;
;; You will first use a bit-blasting encoding for this problem,
;; similar to the approach that I used to generate the example Sudoku
;; problems that I evaluated your DP algorithms using.  What I mean by
;; this is that each Sudoku square will be represented by 9 variables,
;; one for each possible value it may have.
;;
;; A starting board consists of a standard 3x3 Sudoku board with only
;; a subset of cells having specified values. We will use _ to denote
;; unspecified values. The starting board will be represented by a
;; list of 81 elements, where each element can be an integer between 1
;; and 9 inclusive or _.
;;
;; `solve-sudoku` should return an alist mapping Sudoku cell variables
;; (see `sudoku-cell-var` below) to booleans depending on whether the
;; cell represented by the cell variable has the value represented by
;; the cell variable.
;;
;; I have provided the function that generates a variable
;; corresponding to the Sudoku cell at a given row and column having a
;; particular value.
;; row and col should both be integers from 0 to 8, inclusive.
;; val should be an integer from 1 to 9, inclusive.
(defun sudoku-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 9))) "_" (write-to-string val))))

;; I have provided some utilities for pretty-printing Sudoku solutions
;; below.

(defun assoc-equal (x a)
  (assoc x a :test #'equal))

;; Given a solution that is an alist from cell vars to booleans, get
;; the assigned value for the cell at the given row and column, or nil
;; if it is unassigned.
(defun get-square-value (soln row col)
  (block outer
    (loop for i from 1 to 9
          do (when (and (cdr (assoc-equal (sudoku-cell-var row col i) soln))
                        (cadr (assoc-equal (sudoku-cell-var row col i) soln)))
               (return-from outer i)))
    nil))

;; This pretty-prints a Sudoku solution, using `get-square-value` to
;; handle the task of getting the value of a cell from the solution
;; representation used.
(defun pretty-print-3x3-sudoku-solution (soln)
  (loop for row below 9
        do (progn (terpri)
                  (loop for col below 9
                        do (progn (format t "~A " (get-square-value soln row col))
                                  (when (equal (mod col 3) 2) (format t "  "))))
                  (when (equal (mod row 3) 2) (terpri)))))

;; Here's an example starting board. It has a unique solution.
(defconstant *sudoku-example-board*
  '(7 _ _   _ 1 _   _ _ _
    _ 1 _   _ _ 3   7 _ 8
    _ 5 3   _ _ _   _ _ 4

    5 _ 9   3 _ _   _ _ 2
    4 _ 1   2 6 _   3 7 _
    _ _ 7   _ 8 5   9 4 _

    2 7 _   _ 9 4   _ 3 _
    8 _ _   5 _ 1   _ 6 _
    _ 3 _   _ _ 2   4 5 _))

;; Here's its solution.
#|
 7 4 8   9 1 6   5 2 3
 6 1 2   4 5 3   7 9 8
 9 5 3   7 2 8   6 1 4

 5 6 9   3 4 7   1 8 2
 4 8 1   2 6 9   3 7 5
 3 2 7   1 8 5   9 4 6

 2 7 5   6 9 4   8 3 1
 8 9 4   5 3 1   2 6 7
 1 3 6   8 7 2   4 5 9
|#

(defun conjoin (constraints)
  (if constraints
      `(and ,@constraints)
      'true))

(defun at-most-one-constraints (vars)
  (loop for tail on vars append
        (loop for other in (cdr tail)
              collect `(not (and ,(car tail) ,other)))))

(defun exactly-one-constraint (vars)
  (conjoin (cons `(or ,@vars) (at-most-one-constraints vars))))

(defun sudoku-cell-value-vars (row col)
  (loop for val from 1 to 9
        collect (sudoku-cell-var row col val)))

(defun sudoku-bool-var-specs ()
  (loop for row below 9 append
        (loop for col below 9 append
              (loop for val from 1 to 9 append
                    `(,(sudoku-cell-var row col val) :bool)))))

(defun sudoku-cell-exactly-one-constraints ()
  (loop for row below 9 append
        (loop for col below 9 collect
              (exactly-one-constraint (sudoku-cell-value-vars row col)))))

(defun sudoku-row-constraints ()
  (loop for row below 9 append
        (loop for val from 1 to 9 collect
              (exactly-one-constraint
               (loop for col below 9
                     collect (sudoku-cell-var row col val))))))

(defun sudoku-col-constraints ()
  (loop for col below 9 append
        (loop for val from 1 to 9 collect
              (exactly-one-constraint
               (loop for row below 9
                     collect (sudoku-cell-var row col val))))))

(defun sudoku-box-constraints ()
  (loop for box-row below 3 append
        (loop for box-col below 3 append
              (loop for val from 1 to 9 collect
                    (exactly-one-constraint
                     (loop for row from (* box-row 3) below (+ (* box-row 3) 3) append
                           (loop for col from (* box-col 3) below (+ (* box-col 3) 3) collect
                                 (sudoku-cell-var row col val))))))))

(defun sudoku-input-constraints (input-grid)
  (loop for row below 9 append
        (loop for col below 9
              for cell = (nth (+ col (* row 9)) input-grid)
              when (integerp cell)
              collect `(= ,(sudoku-cell-var row col cell) true))))

(defun sudoku-bitblast-constraints (input-grid)
  (conjoin (append (sudoku-cell-exactly-one-constraints)
                   (sudoku-row-constraints)
                   (sudoku-col-constraints)
                   (sudoku-box-constraints)
                   (sudoku-input-constraints input-grid))))

(defun solve-sudoku (input-grid)
  (solver-reset)
  (solver-push)
  (z3-assert-fn (sudoku-bool-var-specs)
                (sudoku-bitblast-constraints input-grid))
  (let ((result (check-sat)))
    (if (equal result :unsat)
        (progn
          (solver-pop)
          'UNSAT)
        (let ((model (get-model-as-assignment)))
          (solver-pop)
          model))))

;; This should print out the solution given above.
(pretty-print-3x3-sudoku-solution (time (solve-sudoku *sudoku-example-board*)))

;; ==========================
;;            Q4
;; ==========================
;; 30 pts
;;
;; 4a. (15 pts)
;;
;; Experiment with a different encoding for Sudoku cells. For example,
;; you could use integers to represent each square, or enumeration
;; sorts. You should define `solve-sudoku-alternate` below to behave
;; like `solve-sudoku` as described in Q3, except that it must use a
;; different encoding to represent the value of each Sudoku cell.
;;
;; You likely will want to define your own version of
;; `sudoku-cell-var`, perhaps omitting the `val` parameter if it is
;; not necessary for your cell value representation.
;;
;; You can continue to use the `pretty-print-3x3-sudoku-solution`
;; function I provided if you redefine `get-square-value` to work with
;; your variable encoding.

;I use an integer encoding
(defun sudoku-cell-var-int (row col)
  (intern (concatenate 'string "Y" (write-to-string (+ col (* row 9))))))

;; Redefine this so pretty-printing works with both encodings.
(defun get-square-value (soln row col)
  (block outer
    ;; First, try the bit-blasted encoding used by solve-sudoku.
    (loop for i from 1 to 9
          for var = (sudoku-cell-var row col i)
          for pair = (assoc-equal var soln)
          do (when (and pair (cadr pair))
               (return-from outer i)))
    ;; If no bit variable was set, try the integer encoding used below.
    (let ((pair (assoc-equal (sudoku-cell-var-int row col) soln)))
      (if pair (cadr pair) nil))))

(defun sudoku-int-var-specs ()
  (loop for row below 9 append
        (loop for col below 9 append
              `(,(sudoku-cell-var-int row col) :int))))

(defun sudoku-int-range-constraints ()
  (loop for row below 9 append
        (loop for col below 9 append
              `((>= ,(sudoku-cell-var-int row col) 1)
                (<= ,(sudoku-cell-var-int row col) 9)))))

(defun sudoku-int-row-constraints ()
  (loop for row below 9 collect
        `(distinct ,@(loop for col below 9
                           collect (sudoku-cell-var-int row col)))))

(defun sudoku-int-col-constraints ()
  (loop for col below 9 collect
        `(distinct ,@(loop for row below 9
                           collect (sudoku-cell-var-int row col)))))

(defun sudoku-int-box-constraints ()
  (loop for box-row below 3 append
        (loop for box-col below 3 collect
              `(distinct
                ,@(loop for row from (* box-row 3) below (+ (* box-row 3) 3) append
                        (loop for col from (* box-col 3) below (+ (* box-col 3) 3) collect
                              (sudoku-cell-var-int row col)))))))

(defun sudoku-int-input-constraints (input-grid)
  (loop for row below 9 append
        (loop for col below 9
              for cell = (nth (+ col (* row 9)) input-grid)
              when (integerp cell)
              collect `(= ,(sudoku-cell-var-int row col) ,cell))))

(defun sudoku-int-constraints (input-grid)
  (conjoin (append (sudoku-int-range-constraints)
                   (sudoku-int-row-constraints)
                   (sudoku-int-col-constraints)
                   (sudoku-int-box-constraints)
                   (sudoku-int-input-constraints input-grid))))

(defun solve-sudoku-alternate (input-grid)
  (solver-reset)
  (solver-push)
  (z3-assert-fn (sudoku-int-var-specs)
                (sudoku-int-constraints input-grid))
  (let ((result (check-sat)))
    (if (equal result :unsat)
        (progn
          (solver-pop)
          'UNSAT)
        (let ((model (get-model-as-assignment)))
          (solver-pop)
          model))))
;this is a much faster encoding!
;bit-blast sees more variables and more clauses and constraints
(pretty-print-3x3-sudoku-solution (time (solve-sudoku-alternate *sudoku-example-board*)))

;; 4b. (15 pts)
;;
;; Compare the performance of `solve-sudoku` and
;; `solve-sudoku-alternate`. Come up with the hardest Sudoku grid you
;; can find for each solver and explain why you think it is hard.
;;
;; Note that Z3 uses a variant of DPLL called DPLL(T) for solving SMT
;; problems.
;;
;; You may find it useful to see internal statistics that Z3 collects
;; during SMT solving. These statistics are cumulative, so you should
;; re-initialize Z3 before each query that you want to measure.
;; These statistics can be printed by calling `(z3::get-solver-stats)`.
;; 
;; Unfortunately there is no single resource that describes what all
;; of the returned statistics means, but some statistics of note are:
;; - :conflicts: the number of conflicts found during DPLL
;; - :decisions: the number of DPLL decisions made
;; - :propagations: the number of times unit propagation was performed
;; - :restarts: the number of times that Z3 decided to restart DPLL
;;   from the beginning, retaining learned conflict clauses (recall
;;   nonchronological backtracking)

;convert z3 stats into alist I can query in benchmark
(defun z3-stats->alist (stats)
  (let* ((ctx (slot-value stats 'z3::context))
         (h (slot-value stats 'z3::handle))
         (n (z3::z3-stats-size ctx h)))
    (loop for i below n
          collect (let* ((k (z3::z3-stats-get-key ctx h i))
                         (v (if (z3::z3-stats-is-uint ctx h i)
                                (z3::z3-stats-get-uint-value ctx h i)
                                (z3::z3-stats-get-double-value ctx h i))))
                    (cons (string-downcase k) v)))))

(defun z3-stat (stats-alist key)
  (cdr (assoc key stats-alist :test #'string=)))


(defun benchmark-sudoku-once (solver-fn board)
  ;; Reinitialize between runs because Z3 stats are cumulative.
  (solver-init)
  (let* ((t0 (get-internal-real-time))
         (res (funcall solver-fn board))
         (t1 (get-internal-real-time))
         (elapsed-ms (* 1000.0 (/ (- t1 t0) internal-time-units-per-second)))
         (stats (z3-stats->alist (z3::get-solver-stats))))
    (list :elapsed-ms elapsed-ms
          :sat (not (equal res 'UNSAT))
          :decisions (or (z3-stat stats "decisions")
                         (z3-stat stats "sat decisions"))
          :conflicts (or (z3-stat stats "conflicts")
                         (z3-stat stats "sat conflicts"))
          :propagations (or (z3-stat stats "propagations")
                            (z3-stat stats "sat propagations nary"))
          :restarts (z3-stat stats "restarts"))))

(defun benchmark-sudoku-average (solver-fn board runs)
  (let ((samples (loop repeat runs collect (benchmark-sudoku-once solver-fn board))))
    (labels ((avg (key)
               (/ (loop for s in samples
                        for v = (getf s key)
                        when (numberp v) sum v)
                  (max 1 (loop for s in samples
                               for v = (getf s key)
                               count (numberp v))))))
      (list :elapsed-ms (avg :elapsed-ms)
            :sat (every (lambda (s) (getf s :sat)) samples)
            :decisions (avg :decisions)
            :conflicts (avg :conflicts)
            :propagations (avg :propagations)
            :restarts (avg :restarts)))))

(defconstant *sudoku-benchmark-candidates*
  (list
   ;; Course-provided example board in this file.
   (cons "example" *sudoku-example-board*)
   ;; Publicly circulated hard puzzle often attributed to Arto Inkala (2012).
   (cons "inkala-2012"
         '(8 _ _   _ _ _   _ _ _
           _ _ 3   6 _ _   _ _ _
           _ 7 _   _ 9 _   2 _ _

           _ 5 _   _ _ 7   _ _ _
           _ _ _   _ 4 5   7 _ _
           _ _ _   1 _ _   _ 3 _

           _ _ 1   _ _ _   _ 6 8
           _ _ 8   5 _ _   _ 1 _
           _ 9 _   _ _ _   4 _ _))
   ;; Publicly circulated hard puzzle known as "AI Escargot".
   (cons "ai-escargot"
         '(1 _ _   _ _ 7   _ 9 _
           _ 3 _   _ 2 _   _ _ 8
           _ _ 9   6 _ _   5 _ _

           _ _ 5   3 _ _   9 _ _
           _ 1 _   _ 8 _   _ _ 2
           6 _ _   _ _ 4   _ _ _

           3 _ _   _ _ _   _ 1 _
           _ 4 _   _ _ _   _ _ 7
           _ _ 7   _ _ _   3 _ _))
   ;; Representative puzzle from the Top95 hard Sudoku family.
   (cons "top95-1"
         '(4 _ _   _ _ _   8 _ 5
           _ 3 _   _ _ _   _ _ _
           _ _ _   7 _ _   _ _ _

           _ 2 _   _ _ _   _ 6 _
           _ _ _   _ 8 _   4 _ _
           _ _ _   _ 1 _   _ _ _

           _ _ _   6 _ 3   _ 7 _
           5 _ _   2 _ _   _ _ _
           1 _ 4   _ _ _   _ _ _))
   ;; Another representative puzzle from the Top95 hard Sudoku family.
   (cons "top95-2"
         '(_ _ _   _ _ _   _ 1 2
           _ _ _   _ _ _   _ _ _
           _ _ 1   _ _ 9   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   5 3 8   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ 5   _ _ 1   _ _ _
           _ _ _   _ _ _   _ _ _
           6 7 _   _ _ _   _ _ _))
   ;; Publicly circulated hard puzzle known as "Platinum Blonde".
   (cons "platinum-blonde"
         '(_ _ _   _ _ 1   _ _ _
           4 _ _   _ _ _   _ _ _
           _ 2 _   _ _ _   _ _ _

           _ _ _   _ 5 _   4 _ 7
           _ _ 8   _ _ _   3 _ _
           _ _ 1   _ 9 _   _ _ _

           3 _ _   4 _ _   2 _ _
           _ 5 _   1 _ _   _ _ _
           _ _ _   8 _ 6   _ _ _))
   ;; Publicly circulated hard puzzle known as "Golden Nugget".
   (cons "golden-nugget"
         '(_ _ _   _ _ _   9 _ 7
           _ _ _   4 2 _   1 8 _
           _ _ _   7 _ 5   _ 2 6

           1 _ _   9 _ 4   _ _ _
           _ 5 _   _ _ _   _ 4 _
           _ _ _   5 _ 7   _ _ 9

           9 2 _   1 _ 8   _ _ _
           _ 3 4   _ 5 9   _ _ _
           5 _ 7   _ _ _   _ _ _))
   ;; From cl-z3 example file: examples/sudoku.lisp (a-hard-sudoku-grid).
   (cons "walter-hard"
         '(6 _ _   3 _ 1   _ 8 4
           _ _ _   _ 6 9   _ _ 7
           _ _ _   _ _ 7   _ 1 3

           4 _ _   6 9 _   _ _ 8
           _ _ _   _ 1 5   _ _ _
           _ _ 8   _ _ _   _ 6 _

           _ _ _   _ _ _   _ _ _
           _ _ _   1 _ _   7 _ _
           2 _ 4   _ _ 3   1 _ _))
   ;; From cl-z3 example file: examples/sudoku.lisp (a-very-hard-sudoku-grid).
   (cons "walter-very-hard"
         '(_ _ _   _ _ _   _ 1 2
           _ _ _   _ _ _   _ _ 3
           _ _ 2   3 _ _   4 _ _

           _ _ 1   8 _ _   _ _ 5
           _ 6 _   _ 7 _   8 _ _
           _ _ _   _ _ 9   _ _ _

           _ _ 8   5 _ _   _ _ _
           9 _ _   _ 4 _   5 _ _
           4 7 _   _ _ 6   _ _ _))
   ;; Structured stress-test from cl-z3 examples/sudoku.lisp.
   (cons "only-first-row-defined"
         '(1 2 3   4 5 6   7 8 9
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _))
   ;; Structured stress-test from cl-z3 examples/sudoku.lisp.
   (cons "only-first-col-defined"
         '(1 _ _   _ _ _   _ _ _
           2 _ _   _ _ _   _ _ _
           3 _ _   _ _ _   _ _ _

           4 _ _   _ _ _   _ _ _
           5 _ _   _ _ _   _ _ _
           6 _ _   _ _ _   _ _ _

           7 _ _   _ _ _   _ _ _
           8 _ _   _ _ _   _ _ _
           9 _ _   _ _ _   _ _ _))
   ;; Structured stress-test from cl-z3 examples/sudoku.lisp.
   (cons "only-diag-defined"
         '(1 _ _   _ _ _   _ _ _
           _ 2 _   _ _ _   _ _ _
           _ _ 3   _ _ _   _ _ _

           _ _ _   4 _ _   _ _ _
           _ _ _   _ 5 _   _ _ _
           _ _ _   _ _ 6   _ _ _

           _ _ _   _ _ _   7 _ _
           _ _ _   _ _ _   _ 8 _
           _ _ _   _ _ _   _ _ 9))
   ;; Structured stress-test from cl-z3 examples/sudoku.lisp.
   (cons "only-first-row-defined-reverse"
         '(9 8 7   6 5 4   3 2 1
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _))))

(defun run-sudoku-benchmarks (&optional (runs 2) (candidates *sudoku-benchmark-candidates*))
  (let ((rows nil))
    (dolist (entry candidates)
      (let* ((name (car entry))
             (board (cdr entry))
             (bit (benchmark-sudoku-average #'solve-sudoku board runs))
             (int (benchmark-sudoku-average #'solve-sudoku-alternate board runs)))
        (push (list :name name :bit bit :int int) rows)
        (format t "~%~A~%  bit: ~,2f ms dec=~A conf=~A prop=~A rest=~A~%  int: ~,2f ms dec=~A conf=~A prop=~A rest=~A~%"
                name
                (getf bit :elapsed-ms) (getf bit :decisions) (getf bit :conflicts)
                (getf bit :propagations) (getf bit :restarts)
                (getf int :elapsed-ms) (getf int :decisions) (getf int :conflicts)
                (getf int :propagations) (getf int :restarts))))
    (setf rows (nreverse rows))
    (let* ((hard-bit (car (sort (copy-list rows) #'> :key (lambda (r) (getf (getf r :bit) :elapsed-ms)))))
           (hard-int (car (sort (copy-list rows) #'> :key (lambda (r) (getf (getf r :int) :elapsed-ms))))))
      (format t "~%~%Hardest for solve-sudoku: ~A (~,2f ms average over ~A run(s)).~%"
              (getf hard-bit :name) (getf (getf hard-bit :bit) :elapsed-ms) runs)
      (format t "Hardest for solve-sudoku-alternate: ~A (~,2f ms average over ~A run(s)).~%"
              (getf hard-int :name) (getf (getf hard-int :int) :elapsed-ms) runs))
    rows))


(run-sudoku-benchmarks 1) ; full sweep
;;(run-sudoku-benchmarks 2 (subseq *sudoku-benchmark-candidates* 0 6)) ;subset sweep

;; The hardest Sudoku board for your `solve-sudoku` implementation.
(defconstant *hardest-sudoku-board*
  '(cons "only-diag-defined"
         '(1 _ _   _ _ _   _ _ _
           _ 2 _   _ _ _   _ _ _
           _ _ 3   _ _ _   _ _ _

           _ _ _   4 _ _   _ _ _
           _ _ _   _ 5 _   _ _ _
           _ _ _   _ _ 6   _ _ _

           _ _ _   _ _ _   7 _ _
           _ _ _   _ _ _   _ 8 _
           _ _ _   _ _ _   _ _ 9))
)

;; The hardest Sudoku board for your `solve-sudoku-alternate`
;; implementation.
(defconstant *hardest-sudoku-board-alternate*
  '(cons "only-first-row-defined"
         '(1 2 3   4 5 6   7 8 9
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _))
  )

;;A more efficient encoding
;;Encoding from the paper https://www.cs.cmu.edu/~hjain/papers/sudoku-as-SAT.pdf
(defun sudoku-3x3-box-index (row col)
  (+ (* (floor row 3) 3) (floor col 3)))

(defun sudoku-build-fixed-info (input-grid)
  (assert (equal (length input-grid) 81))
  (let ((fixed (make-array 81 :initial-element 0))
        (row-has (make-array '(9 10) :initial-element nil))
        (col-has (make-array '(9 10) :initial-element nil))
        (box-has (make-array '(9 10) :initial-element nil))
        (consistent t))
    (loop for row below 9 do
          (loop for col below 9
                for cell = (nth (+ col (* row 9)) input-grid)
                do (when (integerp cell)
                     (when (or (< cell 1) (> cell 9))
                       (setf consistent nil))
                     (let ((box (sudoku-3x3-box-index row col)))
                       (when (or (aref row-has row cell)
                                 (aref col-has col cell)
                                 (aref box-has box cell))
                         (setf consistent nil))
                       (setf (aref fixed (+ col (* row 9))) cell)
                       (setf (aref row-has row cell) t)
                       (setf (aref col-has col cell) t)
                       (setf (aref box-has box cell) t)))))
    (values fixed row-has col-has box-has consistent)))

(defun sudoku-var-status-from-fixed (fixed row-has col-has box-has row col val)
  (let ((given (aref fixed (+ col (* row 9)))))
    (cond
      ;; Variable in V+.
      ((and (> given 0) (equal val given)) :plus)
      ;; Same fixed cell but different value.
      ((> given 0) :minus)
      ;; Value clashes with a given in row/col/box => in V-.
      ((or (aref row-has row val)
           (aref col-has col val)
           (aref box-has (sudoku-3x3-box-index row col) val))
       :minus)
      ;; Unknown variable in V0.
      (t :zero))))

(defun sudoku-v0-var-specs (fixed row-has col-has box-has)
  (let ((specs nil))
    (loop for row below 9 do
          (loop for col below 9 do
                (loop for val from 1 to 9 do
                      (when (equal (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val) :zero)
                        (setf specs (append specs `(,(sudoku-cell-var row col val) :bool)))))))
    specs))

(defun sudoku-row-v0-vars-for-value (fixed row-has col-has box-has row val)
  (loop for col below 9
        when (equal (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val) :zero)
        collect (sudoku-cell-var row col val)))

(defun sudoku-col-v0-vars-for-value (fixed row-has col-has box-has col val)
  (loop for row below 9
        when (equal (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val) :zero)
        collect (sudoku-cell-var row col val)))

(defun sudoku-box-v0-vars-for-value (fixed row-has col-has box-has box-row box-col val)
  (loop for row from (* box-row 3) below (+ (* box-row 3) 3) append
        (loop for col from (* box-col 3) below (+ (* box-col 3) 3)
              when (equal (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val) :zero)
              collect (sudoku-cell-var row col val))))

(defun sudoku-cell-v0-vars (fixed row-has col-has box-has row col)
  (loop for val from 1 to 9
        when (equal (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val) :zero)
        collect (sudoku-cell-var row col val)))

(defun sudoku-optimized-cnf-constraints (fixed row-has col-has box-has)
  (let ((constraints nil)
        (unsat nil))
    ;; Cell definedness/uniqueness (reduced Celld/Cellu over V0).
    (loop for row below 9 do
          (loop for col below 9
                for given = (aref fixed (+ col (* row 9)))
                do (when (equal given 0)
                     (let ((vars (sudoku-cell-v0-vars fixed row-has col-has box-has row col)))
                       (if (endp vars)
                           (setf unsat t)
                           (progn
                             (push `(or ,@vars) constraints)
                             (setf constraints (append (at-most-one-constraints vars) constraints))))))))
    ;; Row definedness/uniqueness.
    (loop for row below 9 do
          (loop for val from 1 to 9
                unless (aref row-has row val) do
                (let ((vars (sudoku-row-v0-vars-for-value fixed row-has col-has box-has row val)))
                  (if (endp vars)
                      (setf unsat t)
                      (progn
                        (push `(or ,@vars) constraints)
                        (setf constraints (append (at-most-one-constraints vars) constraints)))))))
    ;; Column definedness/uniqueness.
    (loop for col below 9 do
          (loop for val from 1 to 9
                unless (aref col-has col val) do
                (let ((vars (sudoku-col-v0-vars-for-value fixed row-has col-has box-has col val)))
                  (if (endp vars)
                      (setf unsat t)
                      (progn
                        (push `(or ,@vars) constraints)
                        (setf constraints (append (at-most-one-constraints vars) constraints)))))))
    ;; Box definedness/uniqueness.
    (loop for box-row below 3 do
          (loop for box-col below 3 do
                (let ((box-idx (+ (* box-row 3) box-col)))
                  (loop for val from 1 to 9
                        unless (aref box-has box-idx val) do
                        (let ((vars (sudoku-box-v0-vars-for-value fixed row-has col-has box-has box-row box-col val)))
                          (if (endp vars)
                              (setf unsat t)
                              (progn
                                (push `(or ,@vars) constraints)
                                (setf constraints (append (at-most-one-constraints vars) constraints)))))))))
    (values (nreverse constraints) unsat)))

(defun sudoku-complete-assignment-from-reduced-model (partial fixed row-has col-has box-has)
  (loop for row below 9 append
        (loop for col below 9 append
              (loop for val from 1 to 9
                    for var = (sudoku-cell-var row col val)
                    for status = (sudoku-var-status-from-fixed fixed row-has col-has box-has row col val)
                    collect
                    (list var
                          (cond
                            ((equal status :plus) t)
                            ((equal status :minus) nil)
                            (t (let ((pair (assoc-equal var partial)))
                                 (if pair (cadr pair) nil)))))))))

(defun solve-sudoku-optimized-cnf (input-grid)
  "Optimized SAT encoding:
compute V+/V-/V0 from givens and solve only over V0."
  (multiple-value-bind (fixed row-has col-has box-has consistent)
      (sudoku-build-fixed-info input-grid)
    (if (not consistent)
        'UNSAT
        (multiple-value-bind (constraints unsat-after-reduction)
            (sudoku-optimized-cnf-constraints fixed row-has col-has box-has)
          (if unsat-after-reduction
              'UNSAT
              (let ((var-specs (sudoku-v0-var-specs fixed row-has col-has box-has)))
                (solver-reset)
                (solver-push)
                ;; If there are no V0 vars, the givens already determine a full board.
                (when var-specs
                  (z3-assert-fn var-specs (conjoin constraints)))
                (let ((result (check-sat)))
                  (if (equal result :unsat)
                      (progn
                        (solver-pop)
                        'UNSAT)
                      (let ((partial (if var-specs (get-model-as-assignment) nil)))
                        (solver-pop)
                        (sudoku-complete-assignment-from-reduced-model
                         partial fixed row-has col-has box-has))))))))))

;;run the benchmark on this solver as well
(defun run-sudoku-benchmarks (&optional (runs 2) (candidates *sudoku-benchmark-candidates*))
  (let ((rows nil))
    (dolist (entry candidates)
      (let* ((name (car entry))
             (board (cdr entry))
             (bit (benchmark-sudoku-average #'solve-sudoku board runs))
             (int (benchmark-sudoku-average #'solve-sudoku-alternate board runs))
             (opt (benchmark-sudoku-average #'solve-sudoku-optimized-cnf board runs)))
        (push (list :name name :bit bit :int int :opt opt) rows)
        (format t "~%~A~%  bit: ~,2f ms dec=~A conf=~A prop=~A rest=~A~%  int: ~,2f ms dec=~A conf=~A prop=~A rest=~A~%  opt: ~,2f ms dec=~A conf=~A prop=~A rest=~A~%"
                name
                (getf bit :elapsed-ms) (getf bit :decisions) (getf bit :conflicts)
                (getf bit :propagations) (getf bit :restarts)
                (getf int :elapsed-ms) (getf int :decisions) (getf int :conflicts)
                (getf int :propagations) (getf int :restarts)
                (getf opt :elapsed-ms) (getf opt :decisions) (getf opt :conflicts)
                (getf opt :propagations) (getf opt :restarts))))
    (setf rows (nreverse rows))
    (let* ((hard-bit (car (sort (copy-list rows) #'> :key (lambda (r) (getf (getf r :bit) :elapsed-ms)))))
           (hard-int (car (sort (copy-list rows) #'> :key (lambda (r) (getf (getf r :int) :elapsed-ms)))))
           (hard-opt (car (sort (copy-list rows) #'> :key (lambda (r) (getf (getf r :opt) :elapsed-ms))))))
      (format t "~%~%Hardest for solve-sudoku: ~A (~,2f ms average over ~A run(s)).~%"
              (getf hard-bit :name) (getf (getf hard-bit :bit) :elapsed-ms) runs)
      (format t "Hardest for solve-sudoku-alternate: ~A (~,2f ms average over ~A run(s)).~%"
              (getf hard-int :name) (getf (getf hard-int :int) :elapsed-ms) runs)
      (format t "Hardest for solve-sudoku-optimized-cnf: ~A (~,2f ms average over ~A run(s)).~%"
              (getf hard-opt :name) (getf (getf hard-opt :opt) :elapsed-ms) runs))
    rows))

(run-sudoku-benchmarks 1)


;;to compare with the hardest grid for the previous solvers
(defconstant *hardest-sudoku-board-optimized-cnf*
  '(cons "only-first-row-defined-reverse"
         '(9 8 7   6 5 4   3 2 1
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _

           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _
           _ _ _   _ _ _   _ _ _)))
     

;; ==========================
;;       Extra Credit
;; ==========================
;; 25pts each

;; ==========================
;;            E1
;; ==========================
;;
;; Extend your Sudoku solver to support arbitrary-size Sudoku
;; puzzles. For n>3, the input and output of your solver should still
;; be numeric (as opposed to e.g. taking in and returning symbols that
;; somehow encode numeric values for cell values greater than 9).

(defun sudoku-side (n)
  (* n n))

(defun sudoku-total-cells (n)
  (let ((side (sudoku-side n)))
    (* side side)))

(defun sudoku-n-cell-var (n row col)
  (let ((side (sudoku-side n)))
    (intern (concatenate 'string "SN" (write-to-string side) "_"
                         (write-to-string (+ col (* row side)))))))

(defun sudoku-n-var-specs (n)
  (let ((side (sudoku-side n)))
    (loop for row below side append
          (loop for col below side append
                `(,(sudoku-n-cell-var n row col) :int)))))

(defun sudoku-n-range-constraints (n)
  (let ((side (sudoku-side n)))
    (loop for row below side append
          (loop for col below side append
                `((>= ,(sudoku-n-cell-var n row col) 1)
                  (<= ,(sudoku-n-cell-var n row col) ,side))))))

(defun sudoku-n-row-constraints (n)
  (let ((side (sudoku-side n)))
    (loop for row below side collect
          `(distinct
            ,@(loop for col below side
                    collect (sudoku-n-cell-var n row col))))))

(defun sudoku-n-col-constraints (n)
  (let ((side (sudoku-side n)))
    (loop for col below side collect
          `(distinct
            ,@(loop for row below side
                    collect (sudoku-n-cell-var n row col))))))

(defun sudoku-n-box-constraints (n)
  (loop for box-row below n append
        (loop for box-col below n collect
              `(distinct
                ,@(loop for row from (* box-row n) below (+ (* box-row n) n) append
                        (loop for col from (* box-col n) below (+ (* box-col n) n) collect
                              (sudoku-n-cell-var n row col)))))))

(defun sudoku-n-input-constraints (n input-grid)
  (let ((side (sudoku-side n)))
    (loop for row below side append
          (loop for col below side
                for cell = (nth (+ col (* row side)) input-grid)
                when (integerp cell)
                collect `(= ,(sudoku-n-cell-var n row col) ,cell)))))

(defun sudoku-n-constraints (n input-grid)
  (conjoin (append (sudoku-n-range-constraints n)
                   (sudoku-n-row-constraints n)
                   (sudoku-n-col-constraints n)
                   (sudoku-n-box-constraints n)
                   (sudoku-n-input-constraints n input-grid))))

(defun sudoku-model->grid (n model)
  (let ((side (sudoku-side n)))
    (loop for row below side append
          (loop for col below side
                for pair = (assoc-equal (sudoku-n-cell-var n row col) model)
                collect (if pair (cadr pair) nil)))))

(defun solve-sudoku-n-z3 (n input-grid)
  "Solve an n^2 x n^2 Sudoku with Z3.
Input: flat list of length (n^4), entries are integers in [1, n^2] or _.
Output: UNSAT or a flat numeric solution list."
  (let ((expected (sudoku-total-cells n)))
    (assert (equal (length input-grid) expected))
    (solver-reset)
    (solver-push)
    (z3-assert-fn (sudoku-n-var-specs n)
                  (sudoku-n-constraints n input-grid))
    (let ((result (check-sat)))
      (if (equal result :unsat)
          (progn (solver-pop) 'UNSAT)
          (let ((model (get-model-as-assignment)))
            (solver-pop)
            (sudoku-model->grid n model))))))

(defun pretty-print-sudoku-n-grid (n grid)
  (let* ((side (sudoku-side n))
         (w (length (write-to-string side))))
    (loop for row below side do
          (progn
            (terpri)
            (loop for col below side do
                  (progn
                    (format t "~vA " w (nth (+ col (* row side)) grid))
                    (when (equal (mod col n) (1- n))
                      (format t " "))))
            (when (equal (mod row n) (1- n))
              (terpri))))))

;; Utility: canonical solved Sudoku of size n^2 x n^2.
;;builds a valid full sudoku pattern
(defun make-canonical-sudoku-solution-grid (n)
  (let ((side (sudoku-side n)))
    (loop for row below side append
          (loop for col below side
                collect (1+ (mod (+ (* row n) (floor row n) col) side))))))

;;turns solution grid into a puzzle by replacing positions in the blank indices with _
(defun make-canonical-sudoku-puzzle-grid (n blank-indices)
  (let ((grid (copy-list (make-canonical-sudoku-solution-grid n))))
    (dolist (idx blank-indices)
      (setf (nth idx grid) '_))
    grid))

(defconstant *sudoku-4x4-example-board*
  (make-canonical-sudoku-puzzle-grid 2 '(1 2 4 7 8 11 13 14)))

(defconstant *sudoku-16x16-example-board*
  (make-canonical-sudoku-puzzle-grid
   4
   '(0 1 2 3 16 17 34 51 68 85 102 119 136 153 170 187 204 221 238 255)))

 ;;make sure you create an example board for whatever n you run!
(pretty-print-sudoku-n-grid 2 (time (solve-sudoku-n-z3 2 *sudoku-4x4-example-board*)))
(pretty-print-sudoku-n-grid 4 (time (solve-sudoku-n-z3 4 *sudoku-16x16-example-board*)))


;; ==========================
;;            E2
;; ==========================
;;
;; Develop a solver for another logic puzzle by encoding it as
;; Z3 assertions using the Lisp-Z3 interface.
;; Any of the logic puzzles here are allowed:
;; https://www.chiark.greenend.org.uk/~sgtatham/puzzles/
;; Any puzzle that is NP-hard is OK.
;;
;; You should provide a short description of the selected logic puzzle
;; and the input encoding you use, as well as a few (2-3) example
;; instances of your chosen puzzle encoded using your input encoding.

;; Puzzle from Simon Tatham's collection: "Mines".
;; Input encoding:
;; - A rectangular grid represented as a list of rows.
;; - Each cell is either an integer clue (0..8) or _ for unknown.
;; - Unknown cells may be mine or safe.
;; - Clue cells are constrained to be safe and have exactly that many
;;   neighboring mines (8-neighborhood).
;; Output:
;; - UNSAT or a solved grid where clues stay numeric and unknowns become
;;   '*' (mine) or '.' (safe).


(defun mines-grid-dimensions (grid)
  (let ((rows (length grid))
        (cols (if grid (length (car grid)) 0)))
    (assert (> rows 0))
    (assert (> cols 0))
    (assert (every (lambda (row) (equal (length row) cols)) grid))
    (values rows cols)))

(defun mines-cell-var (rows cols row col)
  (declare (ignore rows cols))
  (intern (concatenate 'string "M_" (write-to-string row) "_" (write-to-string col))))

(defun mines-var-specs (rows cols)
  (loop for row below rows append
        (loop for col below cols append
              `(,(mines-cell-var rows cols row col) :bool))))

(defun mines-neighbor-coords (rows cols row col)
  (loop for dr in '(-1 0 1) append
        (loop for dc in '(-1 0 1)
              for nr = (+ row dr)
              for nc = (+ col dc)
              when (and (not (and (equal dr 0) (equal dc 0)))
                        (>= nr 0) (< nr rows)
                        (>= nc 0) (< nc cols))
              collect (list nr nc))))

(defun bool-vars-sum (vars)
  (if vars
      `(+ ,@(mapcar (lambda (v) `(ite ,v 1 0)) vars))
      0))

(defun mines-clue-constraints (grid rows cols)
  (loop for row below rows append
        (loop for col below cols
              for cell = (nth col (nth row grid))
              append
              (if (integerp cell)
                  (let* ((mine-var (mines-cell-var rows cols row col))
                         (neighbor-vars
                           (mapcar (lambda (rc)
                                     (mines-cell-var rows cols (first rc) (second rc)))
                                   (mines-neighbor-coords rows cols row col))))
                    `((not ,mine-var)
                      (= ,(bool-vars-sum neighbor-vars) ,cell)))
                  nil))))

(defun solve-mines (grid)
  (multiple-value-bind (rows cols) (mines-grid-dimensions grid)
    (solver-reset)
    (solver-push)
    (z3-assert-fn (mines-var-specs rows cols)
                  (conjoin (mines-clue-constraints grid rows cols)))
    (let ((result (check-sat)))
      (if (equal result :unsat)
          (progn (solver-pop) 'UNSAT)
          (let ((model (get-model-as-assignment)))
            (solver-pop)
            (loop for row below rows collect
                  (loop for col below cols
                        for in-cell = (nth col (nth row grid))
                        if (integerp in-cell)
                        collect in-cell
                        else
                        collect (if (cadr (assoc-equal (mines-cell-var rows cols row col) model))
                                    '*
                                    'safe))))))))

(defun pretty-print-mines-grid (grid)
  (dolist (row grid)
    (format t "~%")
    (dolist (cell row)
      (format t "~A " cell))))

;; Example instances for E2 (all from the above input encoding).
(defconstant *mines-example-1*
  '((_ 2 _)
    (2 4 2)
    (_ 2 _)))

(defconstant *mines-example-2*
  '((_ 1 1 _)
    (1 1 1 1)
    (1 1 1 1)
    (_ 1 1 _)))

(defconstant *mines-example-3*
  '((1 1 2 1 1)
    (1 _ 3 _ 1)
    (2 3 _ 3 2)
    (1 _ 3 _ 1)
    (1 1 2 1 1)))

(pretty-print-mines-grid (time (solve-mines *mines-example-1*)))
(pretty-print-mines-grid (time (solve-mines *mines-example-2*)))
(pretty-print-mines-grid (time (solve-mines *mines-example-3*)))

;; ==========================
;;            E3
;; ==========================
;;
;; Develop your own solver for arbitrary-size Sudoku puzzles.  Try to
;; beat the Z3 version you wrote. There are a lot of Sudoku-specific
;; reasoning shortcuts you can use and you should think carefully
;; about how to manage search. Compare your solver with the Z3 version
;; on a number of interesting examples.

(defun sudoku-box-index (n row col)
  (+ (* (floor row n) n) (floor col n)))
	   
(defun solve-sudoku-n-custom (n input-grid)
  "Backtracking solver with bitset constraints, naked-single propagation,
and MRV branching."
  (let* ((side (sudoku-side n))
         (total (sudoku-total-cells n))
         (all-mask (1- (ash 1 side)))
         (board (make-array total :initial-element 0))
         (row-mask (make-array side :initial-element 0))
         (col-mask (make-array side :initial-element 0))
         (box-mask (make-array side :initial-element 0)))
    (assert (equal (length input-grid) total))
    ;; Initialize from givens.
    (loop for idx below total
          for cell = (nth idx input-grid)
          do (when (integerp cell)
               (when (or (< cell 1) (> cell side))
                 (return-from solve-sudoku-n-custom 'UNSAT))
               (let* ((row (floor idx side))
                      (col (mod idx side))
                      (box (sudoku-box-index n row col))
                      (bit (ash 1 (1- cell))))
                 (when (or (/= 0 (logand (aref row-mask row) bit))
                           (/= 0 (logand (aref col-mask col) bit))
                           (/= 0 (logand (aref box-mask box) bit)))
                   (return-from solve-sudoku-n-custom 'UNSAT))
                 (setf (aref board idx) cell)
                 (setf (aref row-mask row) (logior (aref row-mask row) bit))
                 (setf (aref col-mask col) (logior (aref col-mask col) bit))
                 (setf (aref box-mask box) (logior (aref box-mask box) bit)))))
    (labels
        ((available-mask (idx)
           (let* ((row (floor idx side))
                  (col (mod idx side))
                  (box (sudoku-box-index n row col)))
             (logand all-mask
                     (lognot (logior (aref row-mask row)
                                     (aref col-mask col)
                                     (aref box-mask box))))))
         (single-value-from-mask (mask)
           (loop for val from 1 to side
                 for bit = (ash 1 (1- val))
                 when (/= 0 (logand mask bit))
                 do (return val)))
         (place-value (idx val)
           (let* ((row (floor idx side))
                  (col (mod idx side))
                  (box (sudoku-box-index n row col))
                  (bit (ash 1 (1- val))))
             (cond
               ((equal (aref board idx) val) t)
               ((/= 0 (aref board idx)) nil)
               ((= 0 (logand (available-mask idx) bit)) nil)
               (t
                (setf (aref board idx) val)
                (setf (aref row-mask row) (logior (aref row-mask row) bit))
                (setf (aref col-mask col) (logior (aref col-mask col) bit))
                (setf (aref box-mask box) (logior (aref box-mask box) bit))
                t))))
         (unplace-value (idx val)
           (let* ((row (floor idx side))
                  (col (mod idx side))
                  (box (sudoku-box-index n row col))
                  (bit (ash 1 (1- val))))
             (setf (aref board idx) 0)
             (setf (aref row-mask row) (logand (aref row-mask row) (lognot bit)))
             (setf (aref col-mask col) (logand (aref col-mask col) (lognot bit)))
             (setf (aref box-mask box) (logand (aref box-mask box) (lognot bit)))))
         (undo-placements (placements)
           (dolist (placement placements)
             (unplace-value (first placement) (second placement))))
         (propagate-naked-singles ()
           ;; Returns two values: success? and list of newly forced placements.
           (let ((placements nil)
                 (changed t))
             (loop while changed do
                   (setf changed nil)
                   (loop for idx below total
                         when (equal (aref board idx) 0)
                         do (let ((mask (available-mask idx)))
                              (cond
                                ((equal mask 0)
                                 (undo-placements placements)
                                 (return-from propagate-naked-singles (values nil nil)))
                                ((equal (logcount mask) 1)
                                 (let ((val (single-value-from-mask mask)))
                                   (unless (place-value idx val)
                                     (undo-placements placements)
                                     (return-from propagate-naked-singles (values nil nil)))
                                   (push (list idx val) placements)
                                   (setf changed t)))))))
             (values t placements)))
         (choose-next-cell ()
           ;; MRV: branch on the cell with the fewest candidates.
           (let ((best-idx nil)
                 (best-mask 0)
                 (best-count most-positive-fixnum))
             (loop for idx below total
                   when (equal (aref board idx) 0)
                   do (let* ((mask (available-mask idx))
                             (count (logcount mask)))
                        (when (equal count 0)
                          (return-from choose-next-cell (values -1 0)))
                        (when (< count best-count)
                          (setf best-idx idx)
                          (setf best-mask mask)
                          (setf best-count count))))
             (if best-idx
                 (values best-idx best-mask)
                 (values nil 0))))
         (mask-values (mask)
           (loop for val from 1 to side
                 for bit = (ash 1 (1- val))
                 when (/= 0 (logand mask bit))
                 collect val))
         (search-iterative ()
           ;; Stack frame layout (simple-vector):
           ;; [0]=forced placements from propagation at this node
           ;; [1]=cell idx chosen at this node
           ;; [2]=remaining candidate values to try
           ;; [3]=currently placed candidate (or nil)
           (let ((stack nil)
                 (mode :descend))
             (loop
               do (cond
                    ((equal mode :descend)
                     (multiple-value-bind (ok forced) (propagate-naked-singles)
                       (if (not ok)
                           (setf mode :backtrack)
                           (multiple-value-bind (idx mask) (choose-next-cell)
                             (cond
                               ((equal idx -1)
                                (undo-placements forced)
                                (setf mode :backtrack))
                               ((null idx)
                                (return t))
                               (t
                                (push (vector forced idx (mask-values mask) nil) stack)
                                (setf mode :choose)))))))
                    ((equal mode :choose)
                     (if (endp stack)
                         (return nil)
                         (let ((frame (car stack)))
                           (loop
                             with idx = (aref frame 1)
                             for vals = (aref frame 2) then (aref frame 2)
                             do (if (endp vals)
                                    (progn
                                      (setf mode :backtrack)
                                      (return))
                                    (let ((val (car vals)))
                                      (setf (aref frame 2) (cdr vals))
                                      (when (place-value idx val)
                                        (setf (aref frame 3) val)
                                        (setf mode :descend)
                                        (return))))))))
                    (t ;; :backtrack
                     (loop
                       do (if (endp stack)
                              (return-from search-iterative nil)
                              (let ((frame (car stack)))
                                ;; If a branch value was active, remove it.
                                (let ((active (aref frame 3)))
                                  (when active
                                    (unplace-value (aref frame 1) active)
                                    (setf (aref frame 3) nil)))
                                ;; If node exhausted, pop and undo its forced placements.
                                (if (endp (aref frame 2))
                                    (progn
                                      (undo-placements (aref frame 0))
                                      (pop stack))
                                    (progn
                                      (setf mode :choose)
                                      (return))))))))))))
      (if (search-iterative)
          (loop for idx below total collect (aref board idx))
          'UNSAT))))

(defun compare-custom-vs-z3 (n board &optional (runs 1))
  "Compare solve-sudoku-n-z3 vs solve-sudoku-n-custom on one board."
  (let ((z3-times nil)
        (custom-times nil))
    (loop repeat runs do
          (let ((t0 (get-internal-real-time)))
            (solve-sudoku-n-z3 n board)
            (let ((t1 (get-internal-real-time)))
              (push (* 1000.0 (/ (- t1 t0) internal-time-units-per-second)) z3-times)))
          (let ((t2 (get-internal-real-time)))
            (solve-sudoku-n-custom n board)
            (let ((t3 (get-internal-real-time)))
              (push (* 1000.0 (/ (- t3 t2) internal-time-units-per-second)) custom-times))))
    (let ((z3-avg (/ (apply #'+ z3-times) (length z3-times)))
          (custom-avg (/ (apply #'+ custom-times) (length custom-times))))
      (list :z3-avg-ms z3-avg
            :custom-avg-ms custom-avg
            :custom-faster? (< custom-avg z3-avg)))))

(defparameter *sudoku-36x36-example-board*
  (make-canonical-sudoku-puzzle-grid
   6
   (loop for row below (sudoku-side 6)
         collect (+ (* row (sudoku-side 6)) row))))

(defparameter *sudoku-custom-vs-z3-cases*
  (list
   (list "4x4 example" 2 *sudoku-4x4-example-board* 10)
   (list "9x9 example" 3 *sudoku-example-board* 10)
   (list "9x9 hardest" 3 *hardest-sudoku-board* 3)
   (list "16x16 example" 4 *sudoku-16x16-example-board* 3)
   (list "36x36 example" 6 *sudoku-36x36-example-board* 1)))

(defun normalize-suite-board (board)
  "Accept a few accidental wrapper shapes and return the raw board list."
  (cond
    ;; (\"name\" . <board-list>)
    ((and (consp board) (stringp (car board)))
     (cdr board))
    ;; '(cons \"name\" '(...board...))
    ((and (consp board)
          (eq (car board) 'cons)
          (>= (length board) 3)
          (stringp (second board))
          (consp (third board))
          (eq (first (third board)) 'quote))
     (second (third board)))
    (t board)))

(defun run-custom-vs-z3-suite (&optional runs-or-cases maybe-cases)
  "Run a table-style benchmark suite for solve-sudoku-n-z3 vs solve-sudoku-n-custom.
Usage:
  (run-custom-vs-z3-suite)               ; use default cases and per-case runs
  (run-custom-vs-z3-suite 1)             ; force runs=1 for default cases
  (run-custom-vs-z3-suite custom-cases)  ; custom cases, per-case runs
  (run-custom-vs-z3-suite 2 custom-cases); force runs=2 for custom cases
Each case is (label n board runs)."
  (let* ((forced-runs (and (integerp runs-or-cases) runs-or-cases))
         (raw-cases
           (cond
             ((and runs-or-cases (listp runs-or-cases)) runs-or-cases)
             ((and maybe-cases (listp maybe-cases)) maybe-cases)
             (t *sudoku-custom-vs-z3-cases*)))
         (cases
           (mapcar
            (lambda (case)
              (unless (and (listp case) (>= (length case) 4))
                (error "Invalid suite case: ~S. Expected (label n board runs)." case))
              (destructuring-bind (label n board runs) case
              (unless (and (integerp n) (>= n 2))
                (error "Invalid n in suite case: ~S" case))
              (unless (and (integerp runs) (> runs 0))
                (error "Invalid runs in suite case: ~S" case))
              (let ((board* (normalize-suite-board board)))
                (unless (and (listp board*)
                             (equal (length board*) (sudoku-total-cells n)))
                  (error "Invalid board in suite case ~S: expected flat list length ~A, got ~S"
                         label (sudoku-total-cells n) board))
                (list label n board* (or forced-runs runs)))))
            raw-cases)))
  (format t "~%~A~%" "Case                     n   runs    z3-ms       custom-ms   custom-faster")
  (format t "~A~%"     "--------------------------------------------------------------------------")
  (let ((rows nil))
    (dolist (case cases)
      (destructuring-bind (label n board runs) case
        (let ((res (compare-custom-vs-z3 n board runs)))
          (push (list :label label :n n :runs runs :result res) rows)
          (format t "~A~VT~A~VT~A~VT~,3f~VT~,3f~VT~A~%"
                  label 25 n 30 runs 38
                  (getf res :z3-avg-ms) 50
                  (getf res :custom-avg-ms) 62
                  (if (getf res :custom-faster?) "T" "NIL")))))
    (nreverse rows))))

(run-custom-vs-z3-suite)


;;AI Disclosure
;;I used ChatGPT Codex for
;;Implementing all the benchmarks I used across the pset
;;Used for coding up E3; I gave it a few heuristics to implement I found online + told what dependencies to avoid
;;For searching for problems to use for the benchmark
;;Implementing the optimized cnf from the paper - mostly done by chat except for fixing errors
