From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint ssralg seq choice fintype tuple.
(*Set Implicit Arguments.*)
(*Unset Strict Implicit.*)
Unset Printing Implicit Defensive.

Section Complex.

Variable complex : nat -> Type.

Definition rgrp (n : nat) := complex n -> int.

Definition radd {n : nat} (a b : rgrp n) : rgrp n :=
  fun x => GRing.add (a x) (b x).

Axiom extensional_rgrp : forall (n : nat) (g h : rgrp n), g =1 h <-> g = h.

Lemma raddA {n : nat} : associative (@radd n).
Proof.
  move => x y z.
  apply (proj1 (extensional_rgrp n (radd x (radd y z)) (radd (radd x y) z))).
  move => t.
  rewrite /radd.
  apply GRing.addrA.
Qed.

Lemma raddC {n : nat} : commutative (@radd n).
Proof.
  move => x y.
  apply (proj1 (extensional_rgrp n (radd x y) (radd y x))).
  move => t.
  rewrite /radd.
  apply GRing.addrC.
Qed.

Definition boundsRel (n : nat) := complex n -> complex n.+1 -> int.
Definition boundsRelNZf (n : nat) := complex n.+1 -> list (complex n).
Definition boundsRelNZb (n : nat) := complex n -> list (complex n.+1).

Variable bounds : forall n, boundsRel n.
Variable boundsNZf : forall n, boundsRelNZf n. 
Variable boundsRestrf : forall (n : nat) (f : complex n) (t : complex n.+1),
                          bounds n f t <> 0 -> List.In f (boundsNZf n t).
Variable boundsNZb : forall n, boundsRelNZb n. 
Variable boundsRestrb : forall (n : nat) (f : complex n.+1) (t : complex n),
                          bounds n t f <> 0 -> List.In f (boundsNZb n t).

Definition hdelta {n : nat} (g: rgrp n) : rgrp n.+1 :=
  fun y => foldr (fun (x y : int) => GRing.add x y) 0
           (map (fun z => intRing.mulz (bounds n z y) (g z)) (boundsNZf n y)).

Lemma hdelta_morf {n : nat} (a b : rgrp n): hdelta (radd a b) = radd (hdelta a) (hdelta b).
Proof.
  apply (proj1 (extensional_rgrp _ _ _)).
  move => t.
  rewrite /hdelta.
  rewrite [in RHS]/radd.
  move : (boundsNZf n t).
  elim => //=.
  rewrite !/radd.
  move => a0 l IH.
  rewrite GRing.addrA.
  rewrite [GRing.add _ (intRing.mulz (bounds n a0 t) (b a0))] GRing.addrC.
  rewrite [GRing.add (intRing.mulz (bounds n a0 t) (b a0)) _] GRing.addrA.
  rewrite - GRing.addrA.
  rewrite - IH.
  enough (intRing.mulz (bounds n a0 t) (GRing.add (a a0) (b a0)) = 
          GRing.add (intRing.mulz (bounds n a0 t) (b a0))
                    (intRing.mulz (bounds n a0 t) (a a0))).
  - rewrite H. reflexivity.
  - rewrite !(intRing.mulzC (bounds n a0 t)).
    rewrite intRing.mulz_addl.
    rewrite GRing.addrC.
    reflexivity.
Qed.

Definition haxiom := forall (n : nat) (g: rgrp n) e, hdelta (hdelta g) e = 0.

Variable hconstraint : haxiom.

Definition Ker := forall (n: nat) (e: rgrp n) v, hdelta e v = 0.
Definition Im  := forall (n: nat) (e: rgrp n.+1), exists (x: rgrp n), hdelta x = e.

Record homoType (n: nat) := mkHomoType {
   grp: Type;
   grpOp: grp -> grp -> grp;
   grpOpA: associative grpOp;
   grpOpC: commutative grpOp;
   morf: (rgrp n.+1) -> grp;
   morfCorrect: forall (a b : rgrp n.+1), morf (radd a b) = grpOp (morf a) (morf b);
   morfSur: forall (x: grp), exists (x': rgrp n.+1), morf x' = x;
   factor: forall (x y : rgrp n),
             (morf \o hdelta) x = (morf \o hdelta) y -> hdelta x = hdelta y
}.