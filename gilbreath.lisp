; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
; Data definitions for representing the two halves of the "deck"
(defdata lon (listof nat))
(defdata los (listof symbol))


(check= (lonp '(1 2 3 4)) t)
(check= (losp '(A B C D)) t)
(check= (lonp '(1 2 three 4)) nil)
(check= (losp '(one two 3 four)) nil)
(check= (losp '()) t)
(check= (lonp '()) t)

; common functions from the CS2800 "canon"
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))

; takes two lists and interleaves them such that they alternate between the first list and the second list
; e.g. interleave aaa bbb = ababab
(definec interleave (x :tl y :tl) :tl
  (cond ((endp x) y)
        ((endp y) x)
        (t (cons (car x) (cons (car y) (interleave (cdr x) (cdr y)))))))

(check= (interleave (list 1 1) (list 0 0))
        (list 1 0 1 0))
(check= (interleave (list 1 1) '()) (list 1 1))
(check= (interleave '() '()) '())
(check= (interleave '() (list 1 1)) (list 1 1))
(check= (interleave (list 1 1 1 1) (list 0 0 )) (list 1 0 1 0 1 1))


; custom predicate for telling if something is alternating between symbol and nat
(definec everyotherp (ls :all symb :bool) :bool
  (if (tlp ls)
    (cond
     ((endp ls) t)
     (symb (and (symbolp (car ls)) (everyotherp (cdr ls) nil)))
     ((not symb) (and (rationalp (car ls)) (everyotherp (cdr ls) t))))
    nil))
   


(check= (everyotherp (interleave '(A B C D E) '(1 2 3 4 5)) t)  t)
(check= (everyotherp '() nil) t)
(check= (everyotherp '(A) t) t)
(check= (everyotherp '(A) nil) nil)
(check= (everyotherp '(A 1 B 2 C 3) nil) nil) ;if the symb flag is nil, first item must be a nat

; demonstrates that the reverse of a los is still a los
; used in y-rev2-y-equivalence
(defthm lemma-1
  (implies (losp ls)
           (losp (rev2 ls))))

; demonstrates that the conjecture passes iff (rev2 y) can be simplified to y
(defthm conjecture-1-simp
  (implies (and (lonp x)
                (losp y)
                (equal (len2 x) (len2 y)))
           (everyotherp (interleave x y) nil)))

; created as a rewrite rule to link conjecture-1-simp and conjecture-1
(defthm  y-rev2-y-equivalence
  (implies (and (lonp x)
                (losp y)
                (losp (rev2 y))
                (equal (len2 x) (len2 y)))
           (equal (everyotherp (interleave x y) nil)
                  (everyotherp (interleave x (rev2 y)) nil)))
  :hints (("Goal"
           :use (:instance conjecture-1-simp (x x) (y (rev2 y))))))



; final conjecure, the "goal" of this proof
(defthm conjecture-1
  (implies (and 
            (lonp x) 
            (losp y)
            (equal (len2 x) (len2 y)))
           (everyotherp (interleave x (rev2 y)) nil))
  :rule-classes ((:rewrite))
  :hints (("Goal"
           :in-theory (disable conjecture-1-simp)
           :use (:instance conjecture-1-simp (x x) (y y))
           )))#|ACL2s-ToDo-Line|#

  


