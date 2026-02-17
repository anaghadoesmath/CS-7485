#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
Anagha Gokul ... (put the names of the group members here)

|#

#|

 In this homework, you will use ACL2s to prove theorems.  Think of
 ACL2s as a proof checker. You give it a proof outline and it checks
 it for you.  The high-level idea is that you provide ACL2s with
 theorems (named properties) that can be proved with, ideally, one
 level of induction. ACL2s will take care of the details, so that you
 do not have to, but you are still responsible for coming up with a
 proof outline.

 To use ACL2s effectively, you need to understand how ACL2s works,
 which we covered in class. For example, recall that theorems can be
 of different types; see rule-classes. Most of your theorems will be
 rewrite rules, so make sure you orient them appropriately and follow
 the other guidelines mentioned in class.  Also, you can specify which
 induction to use or any other hints, using the same options as defthm
 takes (see the documentation).

 The main challenge is figuring out which supporting theorems (lemmas)
 you need to prove the top-level theorems. The use of the professional
 method can be very helpful here. 

 When ACL2s gets stuck or some theorem is not going through, use the
 "method" to figure out what ACL2s does not know that will allow it to
 make progress. 

 For all your proofs in this homework, ACL2s should never do nested
 inductions. If it does, specify an appropriate lemma so that nested
 inductions are not needed.

 This homework has some hard problems, so start early and ask
 questions. 

|#

(in-package "ACL2S")
(set-gag-mode nil) ; ACL2s shows what it is doing.

#|

 Start with the configuration below and once you are done with the
 homework, go to the next configuration, cranking up the rigor all the
 way up to (modeling-admit-all). That is, when you submit your
 homework the form below must be (modeling-admit-all), if you want to
 get full credit.

 After (modeling-start), try (modeling-validate-defs), then 
 (modeling-admit-defs) and finally (modeling-admit-all).

 Tip: once you get one configuration working, you can test that there
 were no errors by going to the shell buffer and typing the following.

 (ubt! 1)
 (ld "hwk4.lisp")

 The first form undoes everything and the second loads hwk4.lisp. For
 the ld to work, you must have started acl2s in the directory where
 hwk4 resides, otherwise you have to specify a path. If the ld
 encounters an error, you will see it and you can see where that error
 occurred by typing

 (pbt 0)

 which will show you what events were accepted.

 Once that is working, change the configuration to the next one and do
 it again, fixing problems until done.

 Each problem has its own configuration, which gives you the
 flexibility work on problems in any order and to have different
 levels of rigor per problem, at a given point in time. All
 configurations should be set to (modeling-admit-all) to get full
 credit.

|#

(modeling-start)

#|

Q1. Consider the following definition

|#

;execute only for termination analysis
(definec bad-app (x y acc :tl) :tl
  (declare (xargs
            :termination-method :measure
            :measure (m-bad-app x y acc)
            :well-founded-relation l<
            :otf-flg t
            :hints (("Goal"
                     :do-not-induct t
                     :do-not '(generalize fertilize)
                     :use (m-bad-app-swap-decreases
                           m-bad-app-peel-y-decreases
                           m-bad-app-inner-decreases
                           m-bad-app-outer-decreases)))))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

;for testing
(definec bad-app (x y acc :tl)
  :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))




#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. See the RAP lecture notes on measures; you can use
generalized measure functions.


|#

; Define, m-bad-app, a measure function for bad-app.
; Q1a. We are using the definition on page 133

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q1b. Fill in the definition
(defdata natlist (listof nat))

;idea of using stages given by chatgpt
(definec m-bad-app (x y acc :tl) :natlist
  (declare (ignorable acc))
  (list (if (endp x) 0 1)    ; stage 0: x nonempty
        (if (endp y) 0 1)    ; stage 1: y nonempty (so y=nil is smaller)
        (len y)              ; stage 2: peel y
        (len x)))
;new
(definec m-bad-app (x y acc :all) :natlist
(declare (ignorable acc))
  (list (if (consp x) 1 0)          ; stage: x nonempty?
        (if (consp y) 1 0)          ; stage: y nonempty?
        (acl2-count y)              ; peel y safely even if not a tl
        (acl2-count x)))            ; and x


; The proof obligations for the termination proof of bad-app, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
					; can (and should) prove lemmas as needed.
					; Q1c
(property acl2-count-cdr-decreases (y :all)
  (implies (consp y)
           (< (acl2-count (cdr y))
              (acl2-count y))))


;swap branch decreases
(property m-bad-app-swap-decreases (x acc :all)
  (implies (consp x)
           (l< (m-bad-app nil x acc)
               (m-bad-app x nil acc))))


(property m-bad-app-peel-y-decreases (f :all r acc :all)
  (l< (m-bad-app nil r (cons f acc))
      (m-bad-app nil (cons f r) acc)))


(property m-bad-app-inner-decreases (x y acc :tl)
  (implies (and (consp x) (consp y))
           (l< (m-bad-app acc nil y)
               (m-bad-app x y acc))))
;merge into prev
(property m-bad-app-outer-decreases (x y acc z :tl)
  (implies (and (consp x) (consp y))
           (l< (m-bad-app x nil z)
               (m-bad-app x y acc))))
					; Relate bad-app to app.
; Fill in the ... part below. You can only use functions app, rev, if
; and endp. Make sure that ACL2s can prove the property.

					; Q1d
(definec rev-acc (y acc :tl) :tl
  (if (endp y)
      acc
    (rev-acc (cdr y) (cons (car y) acc))))

(property bad-app-nil-is-rev-acc (y acc :tl)
  (== (bad-app nil y acc)
      (rev-acc y acc)))

(property rev-acc-correct (y acc :tl)
  (== (rev-acc y acc)
      (app (rev y) acc))
  :hints (("Goal" :in-theory (disable rev))))

(property bad-app-nil-x (y acc :tl)
  (== (bad-app nil y acc)
      (app (rev y) acc)))

(property (x y :tl)
  (== (bad-app x y nil)
      (if (endp x)
          (rev y)
        (app (rev x) y))))


; Configuration: update as per instructions
(modeling-start)

#|

Q2. Consider the following definition.

|#
;use for termination
;learnt to use hints using chatgpt - have used the same format throughout
(definec ack (n m :nat) :pos
  :skip-tests t
  (declare (xargs :termination-method :measure
                  :measure (m-ack n m)
                  :well-founded-relation l<
                  :otf-flg t
                  :hints (("Goal"
                           :do-not-induct t
                           :do-not '(generalize fertilize)
                           :use (m-ack-dec-zp-m
                                 m-ack-dec-inner
                                 m-ack-dec-outer)))))
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))


#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. 

|#

; Define, m-ack, a measure function for ack.
; Q2a. We are using the definition on page 133

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q2b. Fill in the definition
(definec m-ack (n m :all) :natlist
  (list (nfix n) (nfix m)))

; The proof obligations for the termination proof of ack, using
; properties.  Make sure that ACL2s can prove all of these
; properties. 

; Q2c
(property m-ack-dec-zp-m (n m :nat)
  (implies (and (not (zp n)) (zp m))
           (l< (m-ack (1- n) 1)
               (m-ack n m))))

(property m-ack-dec-inner (n m :nat)
  (implies (and (not (zp n)) (not (zp m)))
           (l< (m-ack n (1- m))
               (m-ack n m))))

(property m-ack-dec-outer (n m :nat z :all)
  (implies (not (zp n))
           (l< (m-ack (1- n) z)
               (m-ack n m))))


; Configuration: update as per instructions
(modeling-start)

#|

Q3. Consider the following definitions.

|#

(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)

; The :skip-admissibilityp command below tells ACL2s to skip the
; termination proof, as ACL2s cannot prove termination without help.
;use for temrination
(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :measure (m-if-flat x)))
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

#|

 Since match is a macro, it may help to know exactly what it expands
 into. If you aren't familiar with the backquote/comma duo, look it up
 and it may be useful to see what this expands into also. You can
 check using the ":trans1" form, which expands the top-level form one
 time and expands backquote/commas. To fully expand a form you can use
 ":trans" but that expands lets and conds and so on and may not be
 that readable. Try the following

 :trans1 (match x
           (:if-atom x)
           (('if a b c)
            (match a
              (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
              (('if d e f)
               (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))))))

 Notice that the nested match was not expanded, but you can copy that
 form and run trans1 on it to expand it.

|#

; Define, m-if-flat, a measure function for if-flat.
; Q3a. We are using the definition on page 133


; Q3b. Fill in the definition. This definition must be accepted by	; ACL2s.
;sum of the acl2 count of every test position in the tree

;chatgpt helped me come up with measure function
(definec m-if-flat (x :if-expr) :pos
  (match x
    (:if-atom 1)
    (('if a b c)
     (* (m-if-flat a)
        (+ 1 (m-if-flat b) (m-if-flat c))))))

					;HELPERS



; The proof obligations for the termination proof of if-flat, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed. 

					; Q3c
(property m-if-flat-then-branch-decreases (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((b (car (cdr (cdr x)))))
     (l< (m-if-flat b)
         (m-if-flat x)))))

(property m-if-flat-else-branch-decreases (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((c (car (cdr (cdr (cdr x))))))
     (l< (m-if-flat c)
         (m-if-flat x)))))

;chatgpt helped with reasoning abt pushdown
(property m-if-flat-pushdown-decreases (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (and (consp a)
               (eq (car a) 'if)
               (consp (cdr a))
               (consp (cdr (cdr a)))
               (consp (cdr (cdr (cdr a))))
               (eq (cdr (cdr (cdr (cdr a)))) nil))))
   (let ((a (car (cdr x)))
         (b (car (cdr (cdr x))))
         (c (car (cdr (cdr (cdr x))))))
     (let ((d (car (cdr a)))
           (e (car (cdr (cdr a))))
           (f (car (cdr (cdr (cdr a))))))
       (l< (m-if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
           (m-if-flat x))))))



#|
 
 We will now prove that if-flat does not change the semantics of if
 expressions using ideas similar to those from HWK2. We will define
 assignments and an evaluator for if expressions.

|#

(defdata if-assign (alistof var bool))

; Notice that if var is not in the if-assign, we return nil.
(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

; Q3d
; State and prove that for all if-assign's, an if-expr e evaluates to
; the same thing as (if-flat e). This should go though automatically,
; but, remember, you have to provide enough lemmas so that there are
; no nested inductions! Also, remember theorems are rewrite rules, so
; orient appropriately.

;helper
(property if-expr-test-type (x :all y :all)
  (=> (^ (not (consp x))
         (not (varp x))
         (not (booleanp x)))
      (not (if-exprp (list* 'if x y))))
  :hints (("goal" :expand (if-exprp (list* 'if x y)))))

(property if-flat-equal-if (e :if-expr a :if-assign)
  (== (if-eval (if-flat e) a)
      (if-eval e a)))

#|

 Check-validp is a simple validity checker for if-expr's.  The idea is
 to use if-flat to normalize the if-expr. Then, we start with an empty
 if-assign and check validity by traversing the expression. When we
 get to a variable that is not assigned, we check that the expression
 is a validity when the variable is t and when it is nil.

|# 

; Lookup assoc-equal in the documentation.
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))

(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (validp y a)
           (validp z a))
       (and (validp y (acons x t a))
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

; Q3e
; 
; Formalize and prove the soundness of check-validp.  That is, if
; (check-validp e) = t, then evaluating e under a, an arbitrary
; if-assign, results in t.
;ignore redundant assignments
(property if-eval-ignores-redundant-assignments
  (e :if-expr v :var val :bool a :if-assign)
  (=> (== (lookup-var v a) val)
      (== (if-eval e (cons (cons v val) a))
          (if-eval e a))))

(property lookup-app (v :var a :if-assign b :if-assign)
  (== (lookup-var v (append a b))
      (if (assoc-equal v a)
          (lookup-var v a)
        (lookup-var v b))))

(property lookup-assoc (a :if-assign v :var)
  (=> (lookup-var v a)
      (assoc-equal v a)))

(property validp-implies-if-eval (e :norm-if-expr a :if-assign b :if-assign) 
  (=> (validp e b)
      (if-eval e (append b a)))
  :rule-classes nil)

(property check-validp-is-sound (e :if-expr a :if-assign) 
  (=> (check-validp e)
      (if-eval e a))
  :hints (("Goal" :use (:instance validp-implies-if-eval
                                  (e (if-flat e))
                                  (b nil)))))

;acons sets the variable value
(property lookup-var-acons-same (v :var val :bool a :if-assign)
  (== (lookup-var v (acons v val a))
      val)
  :hints (("Goal" :in-theory (enable lookup-var))))

;falsify-h-atom falsifies
(property falsify-h-atom-falsifies (e :if-atom a :if-assign)
  (=> (falsify-h-atom e a)
      (not (if-eval e (falsify-h-atom e a))))
  :hints (("Goal"
           :in-theory (enable falsify-h-atom if-eval lookup-atom lookup-var
                              lookup-var-acons-same))))



(property check-validp-is-sound ...
  ...)

; Configuration: update as per instructions
(modeling-start)


; Q3f
; 
; Prove that check-validp is complete by showing that when
; check-validp returns nil, there is some if-assign under which the
; if-expr evaluates to nil. With this proof, we now know that
; check-validp is a decision procedure for PL validity.
					;helpers that return falsifying assignment
;this part is incomplete
;result pair encoding
(definec res (okp :bool a :if-assign) :tl
  (list okp a))

;recognizer for result pairs
(definec resp (r :tl) :bool
  (match r
    ((okp a) (and (booleanp okp)
                  (if-assignp a)))
    (& nil)))

(definec res-okp (r :tl) :bool
  (if (resp r)
      (car r)
      nil))

(definec res-asg (r :tl) :if-assign
  (if (resp r)
      (cadr r)
    nil))

;falsify-valid-p on normalized expressions

(definec falsify-validp (e :norm-if-expr a :if-assign) :tl
  (match e
    (:if-atom
     (if (lookup-atom e a)
         (res nil nil)
       (res t a)))

    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (falsify-validp y a)
           (falsify-validp z a))
       (if (validp y (acons x t a))
           (falsify-validp z (acons x nil a))
         (falsify-validp y (acons x t a)))))))




;wrapper
(definec falsify (e :if-expr) :tl
  (falsify-validp (if-flat e) nil))


;completion lemmas
;if validp is nil, falsify-valid-p succeeds
(property validp-nil-implies-falsify-ok (e :norm-if-expr a :if-assign)
  (=> (not (validp e a))
      (res-okp (falsify-validp e a)))
  :hints (("Goal"
           :induct (falsify-validp e a)
           :in-theory (enable validp falsify-validp res-okp resp res))))

;semantic correctness
;branch evaluation helpers
(property if-eval-if-when-test-true (x :if-atom y :if-expr z :if-expr a :if-assign)
  (=> (lookup-atom x a)
      (== (if-eval (list 'if x y z) a)
          (if-eval y a)))
  :hints (("Goal" :in-theory (enable if-eval))))

(property if-eval-if-when-test-false (x :if-atom y :if-expr z :if-expr a :if-assign)
  (=> (not (lookup-atom x a))
      (== (if-eval (list 'if x y z) a)
          (if-eval z a)))
  :hints (("Goal" :in-theory (enable if-eval))))

(defthm lookup-var-acons-same
  (implies (and (varp v)
                (boolp val)
                (if-assignp a))
           (equal (lookup-var v (acons v val a))
                  val))
  :hints (("Goal" :in-theory (enable lookup-var))))

(defthm lookup-atom-acons-same
  (implies (and (if-atomp x)
                (not (boolp x))
                (boolp val)
                (if-assignp a))
           (equal (lookup-atom x (acons x val a))
                  val))
  :hints (("Goal"
           :in-theory (enable lookup-atom)
           :use ((:instance lookup-var-acons-same
                            (v x) (val val) (a a))))))

(defthm not-and-elim-right
  (implies (and (not (and p q)) p)
           (not q))
  :rule-classes nil)

(defthm not-and-elim-left
  (implies (and (not (and p q)) q)
           (not p))
  :rule-classes nil)


#|

 Q4. We will now reason about sorting algorithms. Consider the
 following definitions for insert sort and quicksort.

|#

;; See the documentation for <<, which is a total order on the ACL2s
;; universe, so we can compare anything, no matter the types. This
;; allows us to define sorting algorithms that work on integers,
;; rationals, strings, whatever (but using the << ordering).

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x 
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

#|

 Q4. Prove the following property.

 This is not easy, so I strongly recommend that you come up with a
 plan and use the professional method to sketch out a proof.

|#

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))

;helpers
;sortedp over total order
(definec orderedp (x :tl) :bool
  (match x
    (() t)
    ((&) t)                    
    ((a b . r)
     (and (<<= a b)
          (orderedp (cons b r))))))

;helper lemmas
(property less-insert-<< (a b :all l :tl)
  :hyps (and (orderedp l)
             (<< b a))
  (== (insert b (less a l))
      (less a (insert b l))))


(property orderedp-<=-less-a* (a :all l :tl)
  :hyps (and (orderedp l)
             (or (endp l)
                 (<<= a (car l))))
  (== (less a l)
      nil))

(property orderedp-<=-notless-a* (a :all l :tl)
  :hyps (and (orderedp l)
             (or (endp l)
                 (<<= a (car l))))
  (== (notless a l)
      l))


(property less-insert-<<== (a b :all l :tl)
  :hyps (<<= a b)
  (== (less a (insert b l))
      (less a l)))

(property insert-preserves-order (a :all l :tl)
  :hyps (orderedp l)
  (orderedp (insert a l)))


;lemmas
(property L2 (a :all l :tl)
  (== (isort (notless a l))
      (notless a (isort l))))

(property L3 (a :all l :tl)
  :hyps (orderedp l)
  (== (app (less a l)
           (cons a (notless a l)))
      (insert a l)))

(property L4 (l :tl)
  (orderedp (isort l)))
#|

 Extra Credit 1. (25 points each, all or nothing)


 1. First, prove (in ACL2s) that if x and y are ordered true lists,
 under <<=, and permutations of each other, they are equal. Second,
 prove that qsort and isort return ordered permutations of their
 input.
|#

(definec permp (x y :tl) :bool
  (== (isort x)
      (isort y)))

(property isort-ord-idempotent (x :tl)
  :hyps (orderedp x)
  (== (isort x) x))

(property perms-are-equal (x y :tl)
  :hyps (and (orderedp x)
             (orderedp y)
             (permp x y))
  :rule-classes nil
  (== x y))

(property permp-isort-input (x :tl)
  (permp (isort x) x))

(property permp-qsort-input (x :tl)
  (permp (qsort x) x))

;if x and y are ordered true lists, under <<=, and permutations of each other, they are equal
(property ordered-permp->equal (x y :tl)
  :hyps (and (orderedp x)
             (orderedp y)
             (permp x y))
  :rule-classes nil
  (== x y))

;qsort and isort return ordered permutations of input
(property isort-ordered (x :tl)
  (orderedp (isort x)))

(property qsort-ordered (x :tl)
  (orderedp (qsort x)))

#|
 2. Do the homework in another theorem prover of your choice. Try to
 make it as equivalent as possible. Provide a summary of your
 findings.  This is only recommended for those of you that already
 have experience with other theorem provers. ACL2 is not allowed this
 time.
|#






