(declare-datatypes () ((Var Y Z a b)))

(declare-datatypes () ((Lab L1 L2 L3 L4 L5 L6 L?)))

(define-fun En1 ((v!1 Var) (l!1 Lab)) Bool
(or (and (= v!1 Y) (= l!1 L?))
(and (= v!1 Z) (= l!1 L?))
(and (= v!1 a) (= l!1 L?))
(and (= v!1 b) (= l!1 L?))
))

(declare-fun Ex1 (Var Lab) Bool)
(declare-fun En2 (Var Lab) Bool)
(declare-fun Ex2 (Var Lab) Bool)
(declare-fun En3 (Var Lab) Bool)
(declare-fun Ex3 (Var Lab) Bool)
(declare-fun En4 (Var Lab) Bool)
(declare-fun Ex4 (Var Lab) Bool)
(declare-fun En5 (Var Lab) Bool)
(declare-fun Ex5 (Var Lab) Bool)
(declare-fun En6 (Var Lab) Bool)
(declare-fun Ex6 (Var Lab) Bool)

(assert (forall ((v!1 Var) (l!1 Lab))
(ite (= v!1 Y)
(ite (= l!1 L1)
(Ex1 v!1 l!1)
(not (Ex1 v!1 l!1)))
(= (Ex1 v!1 l!1) (En1 v!1 l!1)))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (En2 v!1 l!1) (Ex1 v!1 l!1))))

(assert (forall ((v!1 Var) (l!1 Lab))
(ite (= v!1 Z)
(ite (= l!1 L2)
(Ex2 v!1 l!1)
(not (Ex2 v!1 l!1)))
(= (Ex2 v!1 l!1) (En2 v!1 l!1)))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (En3 v!1 l!1) (Ex2 v!1 l!1))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (En4 v!1 l!1) (Ex3 v!1 l!1))))

(assert (forall ((v!1 Var) (l!1 Lab))
(ite (= v!1 Y)
(ite (= l!1 L4)
(Ex4 v!1 l!1)
(not (Ex4 v!1 l!1)))
(= (Ex4 v!1 l!1) (En4 v!1 l!1)))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (En5 v!1 l!1) (Ex3 v!1 l!1))))

(assert (forall ((v!1 Var) (l!1 Lab))
(ite (= v!1 Z)
(ite (= l!1 L5)
(Ex5 v!1 l!1)
(not (Ex5 v!1 l!1)))
(= (Ex5 v!1 l!1) (En5 v!1 l!1)))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (En6 v!1 l!1) (Ex3 v!1 l!1))))

(assert (forall ((v!1 Var) (l!1 Lab))
(= (Ex6 v!1 l!1) (En6 v!1 l!1))))

(check-sat)

(get-model)

