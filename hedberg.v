From iris.proofmode Require Import tactics.


Section Hedberg.
  Context {A : Type}.

  Definition clas (P : Prop) := ¬ ¬ P -> P.
  Definition dec (P : Prop) := {P} + {¬ P}.

  Definition emb {x y : A} : clas (x = y). Admitted.
  Definition proj {P : Prop} : P -> ¬ ¬ P := λ p f, f p.

  Definition f {x y : A} (p : x = y) : x = y := emb (proj p).

  Context (funext : ∀ A B (f g : A → B), (∀ x, f x = g x) → f = g).

  Lemma dneg_eq {P : Prop} (h1 h2 : ¬ P) : h1 = h2.
  Proof.
    by apply funext.
  Qed.

  Lemma f_eq (x y : A) (p q : x = y) : f p = f q.
  Proof.
    unfold f. f_equal. apply dneg_eq.
  Qed.

  Definition g {x y : A} (p : x = y) : x = y :=
    eq_trans (eq_sym (f (eq_refl x))) p.

  Lemma fg_inv {x y : A} (p : x = y) :
    g (f p) = p.
  Proof.
    unfold g. by destruct p,f.
  Qed.

  Lemma hedberg (x y : A) (p1 p2 : x = y) : p1 = p2.
  Proof.
    rewrite <-(fg_inv p1), <-(fg_inv p2).
    f_equal. apply f_eq.
  Qed.

  Lemma dec_clas P :
    dec P -> clas P.
  Proof.
    intros []?; [|exfalso]; eauto.
  Qed.
End Hedberg.