Require Import Category.Theory.
Require Import Category.Lib.

Set Universe Polymorphism.



Record InhabitedIndexSet := {
  Iset :> Type;
  Ieq_rel : Iset -> Iset -> Prop;
  Ieq_equiv :> Equivalence Ieq_rel;
  Iwitness : Iset; (* Explicit proof of inhabitance *)
}.

Record ArbitrarySet := {
  Jset :> Type;
  Jeq_rel : Jset -> Jset -> Prop;
  Jeq_equiv :> Equivalence Jeq_rel;
}.

Record FilterBase := {
  I : InhabitedIndexSet;
  J : ArbitrarySet;
  F : Iset I -> Jset J -> Prop;

  F_respects_I : forall i1 i2 : Iset I, Ieq_rel I i1 i2 -> 
                forall j : Jset J, F i1 j <-> F i2 j;
  F_respects_J : forall j1 j2 : Jset J, Jeq_rel J j1 j2 -> 
                forall i : Iset I, F i j1 <-> F i j2;
  filter_condition : forall i1 i2 : Iset I, 
    exists k : Iset I, 
      forall j : Jset J, F k j -> (F i1 j /\ F i2 j);
}.

Record FilterBaseMap (FB1 FB2 : FilterBase) := {
  alpha : Jset (J FB1) -> Jset (J FB2) -> Prop; (* The binary relation defining the map *)

  alpha_respects_equivalences : forall j1 j1' j2 j2',
    Jeq_rel (J FB1) j1 j1' -> Jeq_rel (J FB2) j2 j2' ->
    alpha j1 j2 <-> alpha j1' j2';

  (* Ensure totality and functionality on some base set F_i of FB1. This might require
     adjusting the definition to accurately capture the intended mathematical properties,
     such as ensuring there exists at least one j' for every j in the domain of F. *)
  alpha_total_functional : exists i : Iset (I FB1), forall j : Jset (J FB1),
    (F FB1) i j -> exists j' : Jset (J FB2), (alpha j j') /\ 
    (forall j'' : Jset (J FB2), (alpha j j'') -> (Jeq_rel (J FB2)) j' j'');
}.

Record ContinuousFilterBaseMap (FB1 FB2 : FilterBase) := {
  base_map : FilterBaseMap FB1 FB2;  (* Embedding the basic map structure *)

  (* Continuity condition: for each `k` in `FB2`, there exists some `i` in `FB1` such that
     the image of `F_i` under `alpha` is a subset of `F_k'`. *)
  continuity_condition : forall k : Iset (I FB2),
    exists i : Iset (I FB1), forall x : Jset (J FB1),
      F FB1 i x -> exists y : Jset (J FB2), alpha FB1 FB2 base_map x y;
}.

Definition continuous_map_equiv {FB1 FB2 : FilterBase} 
  (f g : ContinuousFilterBaseMap FB1 FB2) : Prop :=
  exists i : Iset (I FB1), forall j : Jset (J FB1), forall l : Jset (J FB2),
    F FB1 i j -> (alpha FB1 FB2 (base_map FB1 FB2 f) j l <-> alpha FB1 FB2 (base_map FB1 FB2 g) j l).

Lemma continuous_map_equiv_refl {FB1 FB2 : FilterBase} :
  Reflexive (@continuous_map_equiv FB1 FB2).
Proof.
  unfold Reflexive. intros. unfold continuous_map_equiv.
  exists (Iwitness _). intros. intuition.
Qed.

Lemma continuous_map_equiv_sym {FB1 FB2 : FilterBase} :
  Symmetric (@continuous_map_equiv FB1 FB2).
Proof.
  unfold Symmetric. intros. unfold continuous_map_equiv.
  unfold continuous_map_equiv in H. destruct H.
  exists x0. intros. specialize (H j l H0). intuition.
Qed.

Lemma continuous_map_equiv_trans {FB1 FB2 : FilterBase} :
  Transitive (@continuous_map_equiv FB1 FB2).
Proof.
  unfold Transitive. intros x y z H H0.
  unfold continuous_map_equiv in H, H0. 
  destruct H as [i H], H0 as [i' H0].

  (* Use filter_condition to find a common i that works for both x -> y and y -> z *)
  destruct (filter_condition FB1 i i') as [k Hk].
  
  exists k. intros j l F_kj. apply Hk in F_kj. destruct F_kj.
  specialize (H j l H1); specialize (H0 j l H2). intuition.
Qed.

Lemma continuous_map_equiv_equiv {FB1 FB2 : FilterBase} :
  Equivalence (@continuous_map_equiv FB1 FB2).
Proof.
  constructor.
  - apply continuous_map_equiv_refl.
  - apply continuous_map_equiv_sym.
  - apply continuous_map_equiv_trans.
Qed.

#[export]
Instance ContinuousMapSetoid {FB1 FB2 : FilterBase} : Setoid (ContinuousFilterBaseMap FB1 FB2) := {
  equiv := continuous_map_equiv;
  setoid_equiv := continuous_map_equiv_equiv
}.

Definition id_alpha {FB : FilterBase} (j1 j2 : Jset (J FB)) : Prop :=
  Jeq_rel (J FB) j1 j2.

Lemma id_alpha_respects_equivalences {FB : FilterBase} :
  forall j1 j1' j2 j2',
    Jeq_rel (J FB) j1 j1' -> Jeq_rel (J FB) j2 j2' ->
    id_alpha j1 j2 <-> id_alpha j1' j2'.
Proof.
  intros j1 j1' j2 j2' Hj1 Hj2.
  unfold id_alpha.
  split; intro H.
  - eapply symmetry in Hj1. eapply transitivity. apply Hj1. eapply transitivity. apply H. apply Hj2.
  - eapply symmetry in Hj2. eapply transitivity. apply Hj1. eapply transitivity. apply H. apply Hj2.
  Unshelve. all: try apply Jeq_equiv.
Qed.

Lemma id_alpha_total_functional {FB : FilterBase} : 
    exists i : Iset (I FB), forall j : Jset (J FB),
    (F FB) i j -> exists j' : Jset (J FB), (id_alpha j j') /\ 
    (forall j'' : Jset (J FB), (id_alpha j j'') -> (Jeq_rel (J FB)) j' j'').
Proof.
  exists (Iwitness _). intros. exists j. split.
  - unfold id_alpha. eapply reflexivity.
  - intros. unfold id_alpha in H0. apply H0.
  Unshelve. apply Jeq_equiv.
Qed.

Definition id_FilterBaseMap (FB : FilterBase) : FilterBaseMap FB FB := {|
  alpha := id_alpha;
  alpha_respects_equivalences := id_alpha_respects_equivalences;
  alpha_total_functional := id_alpha_total_functional
|}.

Lemma id_alpha_continuous {FB : FilterBase} : forall k : Iset (I FB),
    exists i : Iset (I FB), forall x : Jset (J FB),
      F FB i x -> exists y : Jset (J FB), id_alpha x y.
Proof.
  intros. exists k. intros. exists x. unfold id_alpha. eapply reflexivity.
  Unshelve. apply Jeq_equiv.
Qed.

Definition id_ContinuousFilterBaseMap (FB : FilterBase) : 
  ContinuousFilterBaseMap FB FB := {|
  base_map := id_FilterBaseMap FB;
  continuity_condition := id_alpha_continuous
|}.

Definition compose_alpha {FB1 FB2 FB3 : FilterBase}
  (f : FilterBaseMap FB2 FB3) (g : FilterBaseMap FB1 FB2)
  : Jset (J FB1) -> Jset (J FB3) -> Prop :=
  fun j1 j3 => exists j2 : Jset (J FB2), alpha FB1 FB2 g j1 j2 /\ alpha FB2 FB3 f j2 j3.


Definition compose_ContinuousFilterBaseMap {FB1 FB2 FB3 : FilterBase}
  (f : ContinuousFilterBaseMap FB2 FB3) (g : ContinuousFilterBaseMap FB1 FB2)
  : ContinuousFilterBaseMap FB1 FB3 := {|

  base_map := {| alpha := compose_alpha (base_map f) (base_map g); 
                 alpha_respects_equivalences := _ ;  (* Proof required *)
                 alpha_total_functional := _ ;       (* Proof required *)
              |};
  continuity_condition := _                             (* Proof of composed continuity *)

|}.


#[export]
Instance FilterBaseCategory : Category := {
  obj := @FilterBase;

  hom := @ContinuousFilterBaseMap;
  homset := @ContinuousMapSetoid;

  id := id_ContinuousFilterBaseMap;
  
}.


Print FilterBase.
