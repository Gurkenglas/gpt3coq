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

Definition PA_1 (a:Prop) := (forall {a:Prop}, Provable a -> a) -> a.

Theorem npnp : forall {x}, PA_1 (~Provable (~Provable x)).
Proof.
  intros x trust pnp.
  apply trust.
  loebprove.
  contradict H.
  prove.
Qed.

Theorem fairdbotdefect : PA_1 (~Fair <3 Defect).
Proof.
  intros trust cooperates.
  rewrite fixedpoint2 in cooperates.
  apply trust in cooperates.
  rewrite fixedpoint2 in cooperates.
  exact cooperates.
Qed.

(* Take the action for which you can prove the best lower bound. *)
Definition UDT (self other:Prop) := Provable (self -> other) /\ ~Provable (~self -> other).

Lemma composition : forall {a b c:Prop}, (b -> c) -> (a -> b) -> (a -> c). intuition. Qed.
Lemma modus_tollens: forall {p q: Prop}, (p->q) -> ~q -> ~p. auto. Qed.

Theorem theyneverknowUDTcoops : forall b, PA_1(~Provable (UDT <3 b)).
Proof.
  intros d trust.
  unfix.
  refine (_ (npnp trust)). intuition.
  contradict x.
  prove.
  destruct H as [_ u].
  contradict u.
  exact H0.
Qed.

Notation "'UC'" := (UDT <3 UDT).
Lemma UDTdoesntgetexploitedbyUDT : UC <-> ~Provable (~UC -> UC).
Proof. split.
  intro. rewrite fixedpoint2 in H. firstorder.
  intro. unfix. firstorder. prove.
Qed.

Theorem udtcoops : PA_1 UC.
Proof.
  intros trust.
  rewrite UDTdoesntgetexploitedbyUDT.
  refine (modus_tollens (Pmodus _) (theyneverknowUDTcoops UDT trust)).
  prove.
  rewrite UDTdoesntgetexploitedbyUDT.
  rewrite UDTdoesntgetexploitedbyUDT in H.
  firstorder.
Qed.

Theorem prudentunexploitable : forall b, PA_1 (Prudent <3 b -> b <3 Prudent).
Proof. intros b trust pb. assert (eq := pb). rewrite fixedpoint2 in eq. apply trust in eq.
  firstorder.
Qed.

Theorem UDTunexploitable : forall b, PA_1 (UDT <3 b -> b <3 UDT).
Proof. intros b trust ub. assert (ub' := ub). rewrite fixedpoint2 in ub. destruct ub as [notexp _].
  apply trust in notexp. firstorder.
Qed.

Theorem whenPBcoopstheyknow : forall b, Prudent <3 b -> Provable (Prudent <3 b).
  intro b. unfix. intro pb. apply p2pp. firstorder.
Qed.

Theorem prudentudtdefect : PA_1 (~Prudent <3 UDT).
Proof.
  intros trust pu.
  absurd (Provable (UDT <3 Prudent)).
  exact (theyneverknowUDTcoops _ trust).
  assert (pu' := pu).
  rewrite fixedpoint2 in pu'.
  refine (Pmodus _ pu').
  refine (Pmodus _ (whenPBcoopstheyknow _ pu)).
  prove.
Qed.
