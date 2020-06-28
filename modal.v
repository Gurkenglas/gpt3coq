Require Setoid.

Parameter Provable : Prop -> Prop.
Axiom Pmodus : forall {a b:Prop}, Provable (a -> b) -> Provable a -> Provable b.
Axiom loeb : forall {a:Prop}, Provable (Provable a -> a) -> Provable a.
Axiom unsafeNecessitation: forall {a:Prop}, a -> Provable a. (* WRONG *)
Ltac prove := repeat match goal with 
  | [ H : Provable _ |- _ ] => refine (Pmodus _ H); clear H
end; clear; apply unsafeNecessitation; intuition. (* sometimes doesnt clear *)
Ltac loebprove := apply loeb; prove.

Parameter Fixedpoint2 : (Prop -> Prop -> Prop) -> (Prop -> Prop -> Prop) -> Prop. (* SHOULD BE REDUNDANT *)
Notation "A <3 B" := (Fixedpoint2 A B) (at level 70).
Axiom fixedpoint2 : forall {a b}, a <3 b = a (a <3 b) (b <3 a).
Ltac unfix := rewrite fixedpoint2.

Definition Prudent (self other:Prop) := Provable (self <-> other).
Definition Fair    (self other:Prop) := Provable other.
Definition Coop    (self other:Prop) := True.
Definition Defect  (self other:Prop) := False.

Theorem prudentbotcoops : Prudent <3 Prudent. unfix. prove. Qed.

Theorem fairbotcoops : Fair <3 Fair. unfix. loebprove. unfix. prove. Qed.

Theorem p2pp : forall {a : Prop}, Provable a -> Provable (Provable a).
Proof.
  intros a pa.
  refine (Pmodus _ (_: Provable (a /\ Provable a))). prove.
  loebprove. intuition prove.
Qed.

Theorem prudentfaircoops : Prudent <3 Fair.
Proof.
  unfix.
  loebprove.
  unfix. apply p2pp in H. prove. unfix. assumption.
  unfix. exact H.
Qed.

Theorem fairfaircoops : Prudent <3 Fair.
