#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

Anagha (put the names of the group members here)
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
	 (pvars (pvars siff))
	 (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|
 
 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties. 

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t. 

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain
 
 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or x y (foo a b) z (not (foo a b)) w) should be simplified to 

 t 

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.

 
|#
;;helpers
(defun p-neg-formp (x)
  "Recognize literals of form not x"
  (and (consp x)
       (eq (car x) 'not)
       (null (cddr x))))

(defun p-neg-arg (x)
  "extract x"
  (cadr x))

(defun p-atomicp (x)
  "check if x is atomic"
  (and (not (booleanp x))
       (or (symbolp x)
           (and (consp x)
                (not (p-funp (car x)))))))

(defun p-toggle-member (x xs)
  (if (member x xs :test #'equal)
      (remove x xs :test #'equal :count 1)
      (cons x xs)))

(defun p-flatten-op-args (op args)
  (mapcan (lambda (a)
            (if (and (consp a) (eq (car a) op))
                (copy-list (cdr a))
              (list a)))
          args))

(defun p-literal-info (x)
  "Return (values base posp okp) for literals over propositional atoms."
  (cond
    ((p-atomicp x) (values x t t))
    ((and (p-neg-formp x) (p-atomicp (p-neg-arg x)))
     (values (p-neg-arg x) nil t))
    (t (values nil nil nil))))

(defun p-apply-assignments (f amap)
  "Replace occurrences of atoms in amap with booleans and recurse over p-ops."
  (let ((hit (assoc f amap :test #'equal)))
    (cond
      (hit (cdr hit))
      ((booleanp f) f)
      ((symbolp f) f)
      ((p-neg-formp f)
       (let ((h2 (assoc (p-neg-arg f) amap :test #'equal)))
         (if h2
             (not (cdr h2))
           (let ((nx (p-apply-assignments (p-neg-arg f) amap)))
             (if (booleanp nx) (not nx) `(not ,nx))))))
      ((and (consp f) (p-funp (car f)))
       (cons (car f)
             (mapcar (lambda (x) (p-apply-assignments x amap))
                     (cdr f))))
      (t f))))
;;basic simplification for and/or
(defun p-simplify-and-or-basic (op args)
  (let* ((flat (p-flatten-op-args op args))
         (identity (pfun-key->val op :identity))
         (sink (pfun-key->val op :sink))
         (pos nil)
         (neg nil)
         (out nil))
    (block done
      (dolist (a flat)
        (cond
          ((booleanp a)
           (if (equal a sink)
               (return-from done sink)
             nil))
          ((p-neg-formp a)
           (let ((base (p-neg-arg a)))
             (when (member base pos :test #'equal)
               (return-from done sink))
             (unless (member base neg :test #'equal)
               (push base neg)
               (push a out))))
          (t
           (when (member a neg :test #'equal)
             (return-from done sink))
           (unless (member a pos :test #'equal)
             (push a pos)
             (push a out)))))
      (setf out (nreverse out))
      (cond
        ((endp out) identity)
        ((endp (cdr out)) (car out))
        (t (cons op out))))))

;;shannon substitutions from top level literals
(defun p-simplify (f)
  (labels
      ((negate-form (x)
         (cond
           ((booleanp x) (not x))
           ((p-neg-formp x) (p-neg-arg x))
           ((and (consp x) (eq (car x) 'iff))
            (let ((xs (cdr x)))
              (if (endp xs)
                  nil
                  (cons 'iff
                        (cons (negate-form (car xs))
                              (cdr xs))))))
           ((and (consp x) (eq (car x) 'xor))
            (let ((xs (cdr x)))
              (if (endp xs)
                  t
                  (cons 'xor
                        (cons (negate-form (car xs))
                              (cdr xs))))))
           (t `(not ,x))))

       (simplify-and-or (op args)
         (let ((base (p-simplify-and-or-basic op args)))
           (if (or (booleanp base)
                   (not (and (consp base) (eq (car base) op))))
               base
               (let ((lits nil)
                     (others nil)
                     (assigns nil))
                 (dolist (a (cdr base))
                   (multiple-value-bind (b posp okp) (p-literal-info a)
                     (if okp
                         (let ((v (if (eq op 'and)
                                      (if posp t nil)
                                      (if posp nil t))))
                           (push a lits)
                           (push (cons b v) assigns))
                         (push a others))))
                 (if (or (endp assigns) (endp others))
                     base
                     (let* ((lits (nreverse lits))
                            (others (nreverse others))
                            (new-others
                              (mapcar (lambda (x)
                                        (simp1 (p-apply-assignments x assigns)))
                                      others)))
                       (p-simplify-and-or-basic op
                                                (append lits new-others))))))))

       (simplify-parity-op (op args)
         (let* ((flat (p-flatten-op-args op args))
                (identity (pfun-key->val op :identity))
                (flip nil)
                (terms nil))
           (dolist (a flat)
             (cond
               ((booleanp a)
                (unless (equal a identity)
                  (setf flip (not flip))))
               ((p-neg-formp a)
                (setf flip (not flip))
                (setf terms (p-toggle-member (p-neg-arg a) terms)))
               (t
                (setf terms (p-toggle-member a terms)))))
           (setf terms (nreverse terms))
           (let ((core (cond
                         ((endp terms) identity)
                         ((endp (cdr terms)) (car terms))
                         (t (cons op terms)))))
             (if flip
                 (negate-form core)
                 core))))

       (simp1 (x)
         (cond
           ((booleanp x) x)
           ((symbolp x) x)
           ((and (consp x) (p-funp (car x)))
            (let* ((op (car x))
                   (args (mapcar #'simp1 (cdr x))))
              (case op
                (not
                 (negate-form (car args)))

                (and
                 (simplify-and-or 'and args))

                (or
                 (simplify-and-or 'or args))

                (xor
                 (simplify-parity-op 'xor args))

                (iff
                 (simplify-parity-op 'iff args))

                (implies
                 (let ((a (first args))
                       (b (second args)))
                   (cond
                     ((booleanp a) (if a b t))
                     ((booleanp b) (if b t (negate-form a)))
                     ((equal a b) t)
                     (t `(implies ,a ,b)))))

                (if
                 (let ((a (first args))
                       (b (second args))
                       (c (third args)))
                   (cond
                     ((booleanp a) (if a b c))
                     ((equal b c) b)
                     ((and (equal b t) (equal c nil)) a)
                     ((and (equal b nil) (equal c t)) (negate-form a))
                     (t `(if ,a ,b ,c)))))

                (otherwise
                 (cons op args)))))

           ((consp x) x)
           (t x))))

    (loop with cur = f
          for nxt = (simp1 cur)
          until (equal cur nxt)
          do (setf cur nxt)
          finally (return cur))))
;;tests
(assert-acl2s-equal '(and p t (foo t nil) q)
                    (p-simplify '(and p t (foo t nil) q)))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t nil) q))
 '(and p (foo t nil) q))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t b) nil))
 nil)

(assert-acl2s-equal
 '(and p q (and r s) (or u v))
 (p-simplify '(and p q (and r s) (or u v))))

(assert-acl2s-equal
 '(not (not (foo a b)))
 (p-simplify '(not (not (foo a b)))))

(assert-acl2s-equal
 '(not (iff p q r))
 (p-simplify '(not (iff p q r))))

(assert-acl2s-equal
 '(not (xor p q r s))
 (p-simplify '(not (xor p q r s))))


(assert-acl2s-equal
 (p-simplify '(and (or p q) (or r q p) p))
 'p)

(assert-acl2s-equal
 (p-simplify '(or x y (foo a b) z (not (foo a b)) w))
 t)

(assert-acl2s-equal
 '(if p (implies q r) (xor (foo a) s t))
 (p-simplify '(if p (implies q r) (xor (foo a) s t))))


;extra
(assert-acl2s-equal
 '(iff (foo a (if p q r)) p (not p) r)
 (p-simplify '(iff (foo a (if p q r)) p (not p) r)))


(assert-acl2s-equal '(not (iff (and) (or) q))
                    (p-simplify '(not (iff (and) (or) q))))

(assert-acl2s-equal '(and (or (and p q) (not (not r))) (iff s (xor t u)))
                    (p-simplify '(and (or (and p q) (not (not r))) (iff s (xor t u)))))

(assert-acl2s-equal '(and (foo x) (bar y) (not (foo x)))
                    (p-simplify '(and (foo x) (bar y) (not (foo x)))))

;some canonical output checks
(assert (equal (p-simplify '(and p t (foo t nil) q))
               '(and p (foo t nil) q)))

(assert (equal (p-simplify '(and (or p q) (or r q p) p))
               'p))

(assert (equal (p-simplify '(or x y (foo a b) z (not (foo a b)) w))
               t))

#|


 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

(defun ts-negate-lit (lit)
  "Negate a literal/formula at the Tseitin layer."
  (cond
    ((eq lit t) nil)
    ((eq lit nil) t)
    ((p-neg-formp lit) (p-neg-arg lit))
    (t `(not ,lit))))

(defun ts-clause->formula (cl)
  (cond
    ((null cl) nil)
    ((null (cdr cl)) (car cl))
    (t (cons 'or cl))))

(defun ts-clauses->formula (clauses)
  (let ((forms (mapcar #'ts-clause->formula clauses)))
    (cond
      ((null forms) t)
      ((null (cdr forms)) (car forms))
      (t (cons 'and forms)))))

(defun tseitin-unchain (f)
  "Convert n-ary iff/xor to left-associated binary form."
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (if (p-funp op)
         (let ((args (mapcar #'tseitin-unchain args)))
           (if (and (in op '(iff xor)) (> (length args) 2))
               (reduce #'(lambda (acc x) `(,op ,acc ,x))
                       (cddr args)
                       :initial-value `(,op ,(first args) ,(second args)))
             `(,op ,@args)))
       f))
    (_ f)))

(defun tseitin-op-clauses (v op args)
  (case op
    (and
     (append
      (mapcar #'(lambda (a) (list (ts-negate-lit v) a)) args)
      (list (cons v (mapcar #'ts-negate-lit args)))))

    (or
     (append
      (list (cons (ts-negate-lit v) args))
      (mapcar #'(lambda (a) (list v (ts-negate-lit a))) args)))

    (implies
     (let ((a (first args))
           (b (second args)))
       (list (list (ts-negate-lit v) (ts-negate-lit a) b)
             (list v a)
             (list v (ts-negate-lit b)))))

    (iff
     (let ((a (first args))
           (b (second args)))
       (list (list (ts-negate-lit v) (ts-negate-lit a) b)
             (list (ts-negate-lit v) a (ts-negate-lit b))
             (list v (ts-negate-lit a) (ts-negate-lit b))
             (list v a b))))

    (xor
     (let ((a (first args))
           (b (second args)))
       (list (list (ts-negate-lit v) (ts-negate-lit a) (ts-negate-lit b))
             (list (ts-negate-lit v) a b)
             (list v (ts-negate-lit a) b)
             (list v a (ts-negate-lit b)))))

    (if
     (let ((a (first args))
           (b (second args))
           (c (third args)))
       (list (list (ts-negate-lit v) (ts-negate-lit a) b)
             (list (ts-negate-lit v) a c)
             (list v (ts-negate-lit a) (ts-negate-lit b))
             (list v a (ts-negate-lit c)))))

    (otherwise
     (error "Unknown operator in tseitin-op-clauses: ~a" op))))

(defun tseitin-encode-args (args)
  (if (endp args)
      (values nil nil)
    (multiple-value-bind (a cls1) (tseitin-encode (car args))
      (multiple-value-bind (rest cls2) (tseitin-encode-args (cdr args))
        (values (cons a rest) (append cls1 cls2))))))

(defun tseitin-encode (f)
  "Return (values rep clauses)"
  (cond
    ((booleanp f) (values f nil))
    ((p-atomicp f) (values f nil))

    ((p-neg-formp f)
     (multiple-value-bind (rep clauses)
         (tseitin-encode (p-neg-arg f))
       (values (ts-negate-lit rep) clauses)))

    ((and (consp f) (p-funp (car f)))
     (let ((op (car f))
           (args (cdr f)))
       (multiple-value-bind (reps clauses)
           (tseitin-encode-args args)
         (case op
           ;; null/unary cases gone after p-simplify,
           (and
            (cond
              ((endp reps) (values t clauses))
              ((endp (cdr reps)) (values (car reps) clauses))
              (t
               (let ((v (gentemp "TSA")))
                 (values v
                         (append clauses
                                 (tseitin-op-clauses v 'and reps)))))))

           (or
            (cond
              ((endp reps) (values nil clauses))
              ((endp (cdr reps)) (values (car reps) clauses))
              (t
               (let ((v (gentemp "TSO")))
                 (values v
                         (append clauses
                                 (tseitin-op-clauses v 'or reps)))))))

           (implies
            (let ((v (gentemp "TSI")))
              (values v
                      (append clauses
                              (tseitin-op-clauses v 'implies reps)))))

           (iff
            (cond
              ((endp reps) (values t clauses))
              ((endp (cdr reps)) (values (car reps) clauses))
              (t
               (assert (= (length reps) 2) () "iff binary after tseitin-unchain")
               (let ((v (gentemp "TSE")))
                 (values v
                         (append clauses
                                 (tseitin-op-clauses v 'iff reps)))))))

           (xor
            (cond
              ((endp reps) (values nil clauses))
              ((endp (cdr reps)) (values (car reps) clauses))
              (t
               (assert (= (length reps) 2) () "xor binary after tseitin-unchain")
               (let ((v (gentemp "TSX")))
                 (values v
                         (append clauses
                                 (tseitin-op-clauses v 'xor reps)))))))

           (if
            (assert (= (length reps) 3) () "if has arity 3")
            (let ((v (gentemp "TSF")))
              (values v
                      (append clauses
                              (tseitin-op-clauses v 'if reps)))))

           (not
            (assert (= (length reps) 1) () "not should have arity 1")
            (values (ts-negate-lit (first reps)) clauses))

           (otherwise
            (error "Unexpected operator in tseitin-encode: ~a" op))))))

    (t
     (error "Not a propositional formula: ~a" f))))

(defun tseitin (f)
  "Return a CNF formula equisatisfiable with f."
  (let* ((sf (p-simplify f))
         (uf (tseitin-unchain sf)))
    (if (booleanp uf)
        uf
      (multiple-value-bind (root clauses)
          (tseitin-encode uf)
        (cond
          ((eq root t)
           (ts-clauses->formula clauses))
          ((eq root nil)
           nil)
          (t
           (ts-clauses->formula (append clauses (list (list root))))))))))

;helpers
(defun tseitin-literalp (x)
  (or (booleanp x)
      (p-atomicp x)
      (and (p-neg-formp x)
           (p-atomicp (p-neg-arg x)))))

(defun tseitin-clausep (x)
  (or (tseitin-literalp x)
      (and (consp x)
           (eq (car x) 'or)
           (every #'tseitin-literalp (cdr x)))))

(defun tseitin-cnfp (x)
  (or (tseitin-clausep x)
      (and (consp x)
           (eq (car x) 'and)
           (every #'tseitin-clausep (cdr x)))))


(defun tseitin-exists-elim (f vars)
  (if (endp vars)
      (p-simplify f)
    (let* ((v (car vars))
           (ft (p-simplify (p-apply-assignments f (list (cons v t)))))
           (ff (p-simplify (p-apply-assignments f (list (cons v nil))))))
      (tseitin-exists-elim (p-simplify `(or ,ft ,ff))
                           (cdr vars)))))

(defun tseitin-project (f)
  (let* ((cnf (tseitin f))
         (orig (pvars f))
         (aux  (set-difference (pvars cnf) orig :test #'equal)))
    (tseitin-exists-elim cnf aux)))

(defun assert-tseitin-acl2s-equal (f)
  (let ((cnf (tseitin f)))
    (assert (tseitin-cnfp cnf) () "Not CNF: ~a" cnf)
    (assert-acl2s-equal f (tseitin-project f))))

;tests
(assert-tseitin-acl2s-equal '(and p q))
(assert-tseitin-acl2s-equal '(or p (not p)))
(assert-tseitin-acl2s-equal '(and p (not p)))
(assert-tseitin-acl2s-equal '(if p q r))
(assert-tseitin-acl2s-equal '(implies (foo a b) (xor p q r)))
(assert-tseitin-acl2s-equal '(iff p q r s))
(assert-tseitin-acl2s-equal '(or (foo x) (not (foo x))))
(assert-tseitin-acl2s-equal '(and (or p q) (or (not p) r) (or (not r) q)))
(assert-tseitin-acl2s-equal '(and (iff p q) (xor q r) (implies r p)))
(assert-tseitin-acl2s-equal '(xor p q r s t))

;extras
(assert-tseitin-acl2s-equal '(and (or p q) (or (not p) r) (or (not r) q)))
(assert-tseitin-acl2s-equal '(and (iff p q) (xor q r) (implies r p)))
(assert-tseitin-acl2s-equal '(if (foo (if a b c)) (and p q) (or r s)))


#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas. 

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#
;;elpers

(defun cnf-literal-base (lit)
  "Return the underlying atom of a CNF literal."
  (if (p-neg-formp lit)
      (p-neg-arg lit)
      lit))

(defun cnf-literal-negp (lit)
  "Return t iff the CNF literal is negated."
  (p-neg-formp lit))

(defun cnf-normalize-clause (lits)
  "Normalize a cnf clause"
    (block done
    (let ((pos nil)
          (neg nil)
          (out nil))
      (dolist (lit lits)
        (cond
          ((eq lit t)
           (return-from done :taut))

          ((eq lit nil)
           nil)

          ((p-neg-formp lit)
           (let ((base (p-neg-arg lit)))
             (when (member base pos :test #'equal)
               (return-from done :taut))
             (unless (member base neg :test #'equal)
               (push base neg)
               (push lit out))))

          (t
           (when (member lit neg :test #'equal)
             (return-from done :taut))
           (unless (member lit pos :test #'equal)
             (push lit pos)
             (push lit out)))))
      (nreverse out))))

(defun cnf-normalize-clauses (clauses)
  "Normalize a list of CNF clauses"
  (block done
    (let ((out nil))
      (dolist (cl clauses)
        (let ((ncl (cnf-normalize-clause cl)))
          (cond
            ((eq ncl :taut)
             nil)
            ((null ncl)
             (return-from done (list nil)))
            (t
             (push ncl out)))))
      (remove-duplicates (nreverse out) :test #'equal))))


(defun cnf-formula->clause (f)
  (if (and (consp f) (eq (car f) 'or))
      (copy-list (cdr f))
      (list f)))

(defun cnf-formula->clauses (f)
  (let ((sf (p-simplify f)))
    (cond
      ((eq sf t) nil)
      ((eq sf nil) (list nil))
      ((and (consp sf) (eq (car sf) 'and))
       (cnf-normalize-clauses
        (mapcar #'cnf-formula->clause (cdr sf))))
      (t (cnf-normalize-clauses (list (cnf-formula->clause sf)))))))

(defun cnf-assignment-lookup (var assignment)
  (let ((hit (assoc var assignment :test #'equal)))
    (if hit (cdr hit) nil)))

(defun cnf-eval-lit (lit assignment)
  (let ((v (cnf-assignment-lookup (cnf-literal-base lit) assignment)))
    (if (cnf-literal-negp lit) (not v) v)))

(defun cnf-clause-satisfiedp (cl assignment)
  (some (lambda (lit) (cnf-eval-lit lit assignment)) cl))

(defun cnf-satisfiedp (clauses assignment)
  (every (lambda (cl) (cnf-clause-satisfiedp cl assignment)) clauses))

(defun patoms- (f)
  "Return all atoms occurring in F, including non-var atoms."
  (cond
    ((booleanp f) nil)
    ((symbolp f) (list f))
    ((p-neg-formp f) (patoms- (p-neg-arg f)))
    ((and (consp f) (p-funp (car f)))
     (reduce #'append (mapcar #'patoms- (cdr f)) :initial-value nil))
    (t (list f))))

(defun patoms (f)
  "Remove duplicates then return."
  (remove-duplicates (patoms- f) :test #'equal))

(defun dp-complete-assignment (f assignment)
  (let ((out assignment))
    (dolist (a (patoms f) out)
      (unless (assoc a out :test #'equal)
        (push (cons a t) out)))))

(defun dp-assignment-lookup (var assignment)
  (let ((hit (assoc var assignment :test #'equal)))
    (if hit
        (values (cdr hit) t)
      (values nil nil))))


(defun dp-assignment-set (assignment var val)
  (multiple-value-bind (old foundp)
      (dp-assignment-lookup var assignment)
    (cond
      ((not foundp)
       (acons var val assignment))
      ((equal old val)
       assignment)
      (t
       :conflict))))

(defun dp-literal-negate (lit)
  "Negate a CNF literal."
  (if (cnf-literal-negp lit)
      (cnf-literal-base lit)
      `(not ,lit)))

(defun dp-literal-value (lit assignment)
  (multiple-value-bind (v foundp)
      (dp-assignment-lookup (cnf-literal-base lit) assignment)
    (if foundp
        (values (if (cnf-literal-negp lit) (not v) v) t)
	(values nil nil))))

(defun dp-remove-satisfied-clauses (clauses sat-lits)
  (remove-if (lambda (cl)
               (some (lambda (lit) (member lit cl :test #'equal))
                     sat-lits))
             clauses))

(defun dp-choose-var (clauses)
  (cnf-literal-base (car (car clauses))))

(defun dp-pick-assignment (var clauses assignment)
  (if (cnf-satisfiedp clauses (acons var t assignment))
      t
    nil))


;;Profiling Helpers
(defparameter *dp-unit-count* 0)
(defparameter *dp-pure-count* 0)
(defparameter *dp-resolve-count* 0)
(defparameter *dp-call-count* 0)
(defparameter *dp-max-clauses* 0)

(defparameter *dp-time-unit* 0)
(defparameter *dp-time-pure* 0)
(defparameter *dp-time-resolve* 0)
(defparameter *dp-time-solve* 0)
(defparameter *dp-time-total* 0)

(defmacro dp-time (place &body body)
  (let ((start (gensym "START")))
    `(let ((,start (get-internal-real-time)))
       (multiple-value-prog1
           (progn ,@body)
         (incf ,place (- (get-internal-real-time) ,start))))))

(defun dp-stats-reset ()
  (setf *dp-unit-count* 0
        *dp-pure-count* 0
        *dp-resolve-count* 0
        *dp-call-count* 0
        *dp-max-clauses* 0
        *dp-time-unit* 0
        *dp-time-pure* 0
        *dp-time-resolve* 0
        *dp-time-solve* 0
        *dp-time-total* 0))

(defun dp-time->ms (ticks)
  (* 1000.0 (/ ticks internal-time-units-per-second)))

(defun dp-unit (clauses assignment)
  "Repeatedly apply unit propagation.
   Returns (values new-clauses new-assignment conflictp)."
  (dp-time *dp-time-unit*
    (labels ((unit-loop (cls asgn)
               (let ((unit-cl (find-if (lambda (cl) (= (length cl) 1)) cls)))
                 (if (null unit-cl)
                     (values cls asgn nil)
                   (let* ((unit-lit (car unit-cl))
                          (var (cnf-literal-base unit-lit))
                          (val (not (cnf-literal-negp unit-lit)))
                          (neg-lit (dp-literal-negate unit-lit))
                          (new-asgn (dp-assignment-set asgn var val)))
                     (incf *dp-unit-count*)
                     (if (eq new-asgn :conflict)
                         (values (list nil) asgn t)
                       (let* ((cls1 (dp-remove-satisfied-clauses cls (list unit-lit)))
                              (cls2 (mapcar (lambda (cl)
                                              (remove neg-lit cl :test #'equal :count 1))
                                            cls1))
                              (cls3 (cnf-normalize-clauses cls2)))
                         (setf *dp-max-clauses* (max *dp-max-clauses* (length cls3)))
                         (if (member nil cls3 :test #'equal)
                             (values cls3 new-asgn t)
                           (unit-loop cls3 new-asgn)))))))))
      (unit-loop clauses assignment))))

(defun dp-pure (clauses assignment)
  "Repeatedly eliminate pure literals."
  (dp-time *dp-time-pure*
    (labels ((pure-loop (cls asgn)
               (let ((pos nil)
                     (neg nil))
                 (dolist (cl cls)
                   (dolist (lit cl)
                     (let ((v (cnf-literal-base lit)))
                       (if (cnf-literal-negp lit)
                           (pushnew v neg :test #'equal)
                         (pushnew v pos :test #'equal)))))
                 (let ((pure-lits nil)
                       (new-asgn asgn))
                   (dolist (v pos)
                     (unless (member v neg :test #'equal)
                       (push v pure-lits)
                       (setf new-asgn (dp-assignment-set new-asgn v t))
                       (when (eq new-asgn :conflict)
                         (return-from pure-loop (values (list nil) asgn t)))))
                   (dolist (v neg)
                     (unless (member v pos :test #'equal)
                       (push `(not ,v) pure-lits)
                       (setf new-asgn (dp-assignment-set new-asgn v nil))
                       (when (eq new-asgn :conflict)
                         (return-from pure-loop (values (list nil) asgn t)))))
                   (incf *dp-pure-count* (length pure-lits))
                   (if (null pure-lits)
                       (values cls asgn nil)
                     (let ((cls1 (cnf-normalize-clauses
                                  (dp-remove-satisfied-clauses cls pure-lits))))
                       (setf *dp-max-clauses* (max *dp-max-clauses* (length cls1)))
                       (pure-loop cls1 new-asgn)))))))
      (pure-loop clauses assignment))))

(defun dp-resolve (clauses var)
  "Resolve on VAR. Returns the new clause set."
  (dp-time *dp-time-resolve*
    (incf *dp-resolve-count*)
    (let ((pos-lit var)
          (neg-lit `(not ,var))
          (pos nil)
          (neg nil)
          (rest nil))
      (dolist (cl clauses)
        (cond
          ((member pos-lit cl :test #'equal) (push cl pos))
          ((member neg-lit cl :test #'equal) (push cl neg))
          (t (push cl rest)))).
      (let ((resolvents nil))
        (dolist (cp pos)
          (dolist (cn neg)
            (push (append (remove pos-lit cp :test #'equal :count 1)
                          (remove neg-lit cn :test #'equal :count 1))
                  resolvents)))
        (let ((next (cnf-normalize-clauses (append rest resolvents))))
          (setf *dp-max-clauses* (max *dp-max-clauses* (length next)))
          next)))))

(defun dp-solve-clauses (clauses &optional (assignment nil))
  "Main DP loop with unit propagation, pure literals, and resolution.
   Returns (values status assignment)."
  (dp-time *dp-time-solve*
    (incf *dp-call-count*)
    (let ((cls (cnf-normalize-clauses clauses)))
      (setf *dp-max-clauses* (max *dp-max-clauses* (length cls)))
      (cond
        ((null cls)
         (values 'sat assignment))
        ((member nil cls :test #'equal)
         (values 'unsat nil))
        (t
         (multiple-value-bind (cls1 asgn1 conflict1)
             (dp-unit cls assignment)
           (setf *dp-max-clauses* (max *dp-max-clauses* (length cls1)))
           (cond
             (conflict1
              (values 'unsat nil))
             ((null cls1)
              (values 'sat asgn1))
             ((member nil cls1 :test #'equal)
              (values 'unsat nil))
             (t
              (multiple-value-bind (cls2 asgn2 conflict2)
                  (dp-pure cls1 asgn1)
                (setf *dp-max-clauses* (max *dp-max-clauses* (length cls2)))
                (cond
                  (conflict2
                   (values 'unsat nil))
                  ((null cls2)
                   (values 'sat asgn2))
                  ((member nil cls2 :test #'equal)
                   (values 'unsat nil))
                  (t
                   (let* ((v (dp-choose-var cls2))
                          (next (dp-resolve cls2 v)))
                     (multiple-value-bind (status rec-assignment)
                         (dp-solve-clauses next asgn2)
                       (if (eq status 'unsat)
                           (values 'unsat nil)
                         (let ((val (dp-pick-assignment v cls2 rec-assignment)))
                           (values 'sat (acons v val rec-assignment)))))))))))))))))

(defun dp (f)
  "Run Davis-Putnam on a CNF formula F."
  (dp-time *dp-time-total*
    (multiple-value-bind (status assignment)
        (dp-solve-clauses (cnf-formula->clauses f))
      (if (eq status 'sat)
          (values 'sat (dp-complete-assignment f assignment))
        (values 'unsat nil)))))

;;run DP on formulas by Tseitin CNF
;;don't use this anymore
(defun dp* (f)
  (dp (tseitin f)))

;;DP corrrectness checker
;;If DP says unsat, check f == nil.
;;If DP says sat with assignment A, check (and f A) == A.

(defun solver-status (solver f)
  (car (multiple-value-list (funcall solver f))))

;; Build a conjunction of literals from a solver assignment alist.
(defun assignment->formula (assignment)
  "Convert an assignment alist into a conjunction of literals."
  (let ((lits
         (mapcar (lambda (kv)
                   (if (cdr kv)
                       (car kv)
                     `(not ,(car kv))))
                 assignment)))
    (cond
      ((null lits) t)
      ((null (cdr lits)) (car lits))
      (t (cons 'and lits)))))


(defun assert-dp-correct (f)
  "Check that DP returns the right status and, if SAT, a satisfying total assignment."
  (multiple-value-bind (status assignment) (dp f)
    (cond
      ((eq status 'unsat)
       (assert-acl2s-equal f nil))
      ((eq status 'sat)
       ;; Every atom should be assigned.
       (assert (every (lambda (a) (assoc a assignment :test #'equal))
                      (patoms f)))
       ;; Returned assignment should satisfy f.
       (let ((amodel (assignment->formula assignment)))
         (assert-acl2s-equal `(and ,f ,amodel) amodel)))
      (t
       (error "Unexpected DP status: ~a" status)))))
;;Tests
(assert-dp-correct '(and (or p q) (or (not p) r)))
(assert-dp-correct '(and p (not p)))
(assert-dp-correct '(and (or p) (or (not p))))
(assert-dp-correct '(and (or p q) (or (not q) r) (or (not r))))
(assert-dp-correct '(and (or (foo a b)) (or (not (foo a b)))))
(assert-dp-correct '(and (or p q r) (or (not p) q) (or (not q) r)))
(assert-dp-correct '(and (or p) (or q) (or (not p) (not q))))
(assert-dp-correct '(and (or (foo (if a b)) x)
                         (or (not (foo (if a b))) y)
                         (or (not y) x)))
(assert-dp-correct '(and (or p (not q))
                         (or q)
                         (or (not p) r)
                         (or (not r) q)))
(assert-dp-correct '(and (or (bar u) (not (baz v)))
                         (or (baz v))
                     (or (not (bar u)))))
;;status tests
(assert (equal (car (multiple-value-list (dp '(and p (not p))))) 'unsat))
(assert (equal (car (multiple-value-list (dp '(and (or p q) (or (not p) r))))) 'sat))

#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#

;;4a
(defun dp-stats-report (f rounds)
  "Print profiling stats for DP on F over ROUNDS runs."
  (format t "~%=== DP profiling report ===~%")
  (format t "Formula: ~S~%" f)
  (format t "Rounds: ~D~%" rounds)
  (format t "Atoms: ~D~%" (length (patoms f)))
  (format t "Clauses: ~D~%" (length (cnf-formula->clauses f)))
  (format t "Recursive calls: ~D~%" *dp-call-count*)
  (format t "Max clauses seen: ~D~%" *dp-max-clauses*)
  (format t "Unit propagations: ~D~%" *dp-unit-count*)
  (format t "Pure eliminations: ~D~%" *dp-pure-count*)
  (format t "Resolution steps: ~D~%" *dp-resolve-count*)
  (format t "Unit time: ~,3F ms~%" (dp-time->ms *dp-time-unit*))
  (format t "Pure time: ~,3F ms~%" (dp-time->ms *dp-time-pure*))
  (format t "Resolve time: ~,3F ms~%" (dp-time->ms *dp-time-resolve*))
  (format t "Solve time: ~,3F ms~%" (dp-time->ms *dp-time-solve*))
  (format t "Total time: ~,3F ms~%" (dp-time->ms *dp-time-total*))
  (format t "===========================~%"))

(defun profile-dp-one (f &optional (rounds 100))
  "Run DP on F repeatedly and print profiling statistics."
  (dp-stats-reset)
  (format t "~%Profiling DP on: ~S~%" f)
  (dotimes (i rounds)
    (dp f))
  (dp-stats-report f rounds))

(defun profile-dp ()
  "Profile DP on a few CNF formulas."
  (profile-dp-one
   '(and (or p q)
         (or (not p) r)
         (or (not r) s)
         (or (not s) q))
   200)

  (profile-dp-one
   '(and (or p q r)
         (or (not p) (not q))
         (or (not r) q)
         (or p (not r)))
   200)

  (profile-dp-one
   '(and (or (foo (if a b)) x)
         (or (not (foo (if a b))) y)
         (or (not y) x))
   200)

  (profile-dp-one
   '(and p (not p))
   200))


;;tests for profiler
(assert (equal (solver-status #'dp '(and (or p q) (or (not p) r))) 'sat))
(assert (equal (solver-status #'dp '(and p (not p))) 'unsat))
(assert (equal (solver-status #'dp '(and (or p) (or (not p)))) 'unsat))
(assert (equal (solver-status #'dp '(and (or p q) (or (not q) r) (or (not r)))) 'sat))
(assert (equal (solver-status #'dp '(and (or (foo a b)) (or (not (foo a b))))) 'unsat))

(profile-dp)

;;DPLL
(defun dpll-set-union (a b)
  (remove-duplicates (append a b) :test #'equal))

;; info is an alist
(defun dpll-info-get (info var)
  (let ((hit (assoc var info :test #'equal)))
    (if hit
        (values t (second hit) (third hit))
      (values nil nil nil))))

(defun dpll-info-set (info var val deps)
  (acons var
         (list val (remove-duplicates deps :test #'equal))
         (remove var info :key #'car :test #'equal)))

(defun dpll-info->assignment (info)
  (mapcar (lambda (e) (cons (car e) (second e))) info))

(defun dpll-analyze-clause (cl info)
  (let ((unassigned nil)
        (false-deps nil))
    (dolist (lit cl)
      (let ((var (cnf-literal-base lit)))
        (multiple-value-bind (found val deps) (dpll-info-get info var)
          (if (not found)
              (push lit unassigned)
            (if (if (cnf-literal-negp lit) (not val) val)
                (return-from dpll-analyze-clause (values :sat nil nil))
              (setf false-deps (dpll-set-union false-deps deps)))))))
    (cond
      ((null unassigned) (values :conflict nil false-deps))
      ((null (cdr unassigned)) (values :unit (car unassigned) false-deps))
      (t (values :open nil nil)))))

(defun dpll-find-pure-unassigned (clauses info)
  (let ((pos nil)
        (neg nil))
    (dolist (cl clauses)
      (multiple-value-bind (status ign1 ign2) (dpll-analyze-clause cl info)
        (declare (ignore ign1 ign2))
        (unless (eq status :sat)
          (dolist (lit cl)
            (let ((var (cnf-literal-base lit)))
              (multiple-value-bind (found ign3 ign4) (dpll-info-get info var)
                (declare (ignore ign3 ign4))
                (unless found
                  (if (cnf-literal-negp lit)
                      (pushnew var neg :test #'equal)
                    (pushnew var pos :test #'equal)))))))))
    (dolist (v pos (values nil nil nil))
      (unless (member v neg :test #'equal)
        (return (values v t t))))
    (dolist (v neg (values nil nil nil))
      (unless (member v pos :test #'equal)
        (return (values v nil t))))))

(defun dpll-propagate (clauses info)
  (let ((cur info))
    (loop
      (let ((unit-lit nil)
            (unit-deps nil)
            (conflict-seen nil)
            (conflict-deps nil))
        (block scan
          (dolist (cl clauses)
            (multiple-value-bind (status lit deps)
                (dpll-analyze-clause cl cur)
              (case status
                (:conflict
                 (setf conflict-seen t)
                 (setf conflict-deps deps)
                 (return-from scan nil))
                (:unit
                 (unless unit-lit
                   (setf unit-lit lit)
                   (setf unit-deps deps)))))))
        (when conflict-seen
          (return (values :conflict cur conflict-deps)))
        (if unit-lit
            (let* ((var (cnf-literal-base unit-lit))
                   (val (not (cnf-literal-negp unit-lit))))
              (multiple-value-bind (found old-val old-deps)
                  (dpll-info-get cur var)
                (cond
                  ((not found)
                   (setf cur (dpll-info-set cur var val unit-deps)))
                  ((equal old-val val) nil)
                  (t
                   (return (values :conflict
                                   cur
                                   (dpll-set-union old-deps unit-deps)))))))
          (multiple-value-bind (pvar pval okp)
              (dpll-find-pure-unassigned clauses cur)
            (if okp
                (setf cur (dpll-info-set cur pvar pval nil))
              (return (values :ok cur nil)))))))))

(defun dpll-all-satisfied-p (clauses info)
  (every (lambda (cl)
           (multiple-value-bind (status ign1 ign2) (dpll-analyze-clause cl info)
             (declare (ignore ign1 ign2))
             (eq status :sat)))
         clauses))

(defun dpll-choose-var (clauses info)
  (let ((best-var nil)
        (best-len nil))
    (dolist (cl clauses best-var)
      (multiple-value-bind (status ign1 ign2) (dpll-analyze-clause cl info)
        (declare (ignore ign1 ign2))
        (unless (eq status :sat)
          (let ((count 0)
                (first-var nil))
            (dolist (lit cl)
              (let ((var (cnf-literal-base lit)))
                (multiple-value-bind (found ign3 ign4) (dpll-info-get info var)
                  (declare (ignore ign3 ign4))
                  (unless found
                    (incf count)
                    (unless first-var (setf first-var var))))))
            (when (and first-var
                       (or (null best-len) (< count best-len)))
              (setf best-var first-var)
              (setf best-len count))))))))

(defun dpll-preferred-value (var clauses info)
  (let ((pos 0)
        (neg 0))
    (dolist (cl clauses)
      (multiple-value-bind (status ign1 ign2) (dpll-analyze-clause cl info)
        (declare (ignore ign1 ign2))
        (unless (eq status :sat)
          (dolist (lit cl)
            (when (equal (cnf-literal-base lit) var)
              (if (cnf-literal-negp lit) (incf neg) (incf pos)))))))
    (>= pos neg)))

(defun dpll-make-frame (var first-val alt-val base-info)
  (list :var var
        :first first-val
        :alt alt-val
        :base base-info
        :c1 nil
        :alt-tried nil))

(defun dpll-handle-conflict (conflict-set info stack)
  (let ((cset conflict-set)
        (cur info)
        (frames stack))
    (loop
      (when (null frames)
        (return (values :unsat nil nil)))
      (let* ((fr (car frames))
             (var (getf fr :var))
             (base (getf fr :base)))
        (cond
          ((getf fr :alt-tried)
           (let ((merged (dpll-set-union cset (getf fr :c1))))
             (setf cset (remove var merged :test #'equal))
             (setf frames (cdr frames))
             (setf cur base)))
          ((member var cset :test #'equal)
           (setf (getf fr :alt-tried) t)
           (setf (getf fr :c1) cset)
           (setf frames (cons fr (cdr frames)))
           (setf cur (dpll-info-set base var (getf fr :alt) (list var)))
           (return (values :resume cur frames)))
          (t
           (setf frames (cdr frames))
           (setf cur base)))))))

(defun dpll (f)
  (let ((clauses (cnf-formula->clauses f))
        (info nil)
        (stack nil))
    (loop
      (multiple-value-bind (status ninfo conflict-set)
          (dpll-propagate clauses info)
        (cond
          ((eq status :conflict)
           (multiple-value-bind (hstatus hinfo hstack)
               (dpll-handle-conflict conflict-set ninfo stack)
             (if (eq hstatus :unsat)
                 (return (values 'unsat nil))
               (progn
                 (setf info hinfo)
                 (setf stack hstack)))))
          (t
           (setf info ninfo)
           (if (dpll-all-satisfied-p clauses info)
               (return (values 'sat
                               (dp-complete-assignment f
                                                       (dpll-info->assignment info))))
             (let* ((var (dpll-choose-var clauses info))
                    (val (dpll-preferred-value var clauses info))
                    (alt (not val))
                    (fr (dpll-make-frame var val alt info)))
               (push fr stack)
               (setf info (dpll-info-set info var val (list var)))))))))))

(defun assert-dpll-correct (f)
  (multiple-value-bind (status assignment) (dpll f)
    (cond
      ((eq status 'unsat)
       (assert-acl2s-equal f nil))
      ((eq status 'sat)
       (assert (every (lambda (a) (assoc a assignment :test #'equal))
                      (patoms f)))
       (let ((amodel (assignment->formula assignment)))
         (assert-acl2s-equal `(and ,f ,amodel) amodel)))
      (t
       (error "Unexpected DPLL status: ~a" status)))))

;;Tests
(assert-dpll-correct '(and (or p q) (or (not p) r)))
(assert-dpll-correct '(and (or p q) (or (not q) r) (or (not r))))
(assert-dpll-correct '(and (or p q r) (or (not p) q) (or (not q) r)))
(assert-dpll-correct '(and (or (foo (if a b)) x)
                           (or (not (foo (if a b))) y)
                           (or (not y) x)))
(assert-dpll-correct '(and (or p (not q)) (or q) (or (not p) r) (or (not r) q)))
(assert-dpll-correct '(and p (not p)))
(assert-dpll-correct '(and (or p) (or (not p))))
(assert-dpll-correct '(and (or (foo a b)) (or (not (foo a b)))))
(assert-dpll-correct '(and (or p) (or q) (or (not p) (not q))))
(assert-dpll-correct '(and (or (bar u) (not (baz v)))
                           (or (baz v))
                           (or (not (bar u)))))


#|
AI Usage Disclosure: I used ChatGPT/Codex for the following:
1. Profiling arguments: I was not quite sure what to do so it helped me come up with appropriate metrics to be considered. I implemented the more simpler metrics. So I would say 50% of the profiling was done by Codex.The 
2. Helped in debugging p-simplify where I had created a loop because of which larger inputs were failing.
3.Suggested using unchaining arguments for tseitin which I implemented.
4. Helped in reformatting and restructuring code.
5. The test cases are almost completely AI generated but I suggested heuristics.

Overall I would say 30-35% of the intellectual input came from genAI for this assignment.
|#
