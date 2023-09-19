
section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  := by
  intros p notp
  have hboom: False := notp p
  exact hboom

theorem doubleneg_elim :
  ¬¬P → P  := by 
  intro notnotp
  by_cases p: P
  exact p
  apply False.elim (notnotp p)

theorem doubleneg_law :
  ¬¬P ↔ P  := by
  apply Iff.intro
  exact doubleneg_elim P
  exact doubleneg_intro P

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hpq
  apply Or.elim hpq
  intro p
  apply Or.inr
  exact p
  intro q
  apply Or.inl
  exact q

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  apply And.intro
  exact And.right hpq
  exact And.left hpq

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  := by
  intro hnpq
  intro p
  apply Or.elim hnpq
  intro notp
  apply False.elim (notp p)
  intro q
  exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  := by
  intro hpq
  intro notp
  apply Or.elim hpq
  intro p
  apply False.elim (notp p)
  intro q
  exact q

------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  := by
  intro hpq
  intro notq
  intro p
  have q: Q := hpq p
  apply False.elim (notq q)

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := by
  intro hnqnp
  intro p
  by_cases q: Q
  exact q
  have notp: ¬P := hnqnp q
  apply False.elim (notp p)

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  := by
  apply Iff.intro
  exact impl_as_contrapositive P Q
  exact impl_as_contrapositive_converse P Q

------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  := by
  intro nhpnp
  suffices hpnp: (P∨¬P) from nhpnp hpnp
  apply Or.inr
  intro p
  suffices hpnp: (P∨¬P) from nhpnp hpnp
  apply Or.inl
  exact p

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  := by
  intro hpqp
  intro notp
  suffices hpq: (P → Q) from False.elim (notp (hpqp hpq))
  intro p
  apply False.elim (notp p)

theorem peirce_law :
  ((P → Q) → P) → P  := by
  intro hpqp
  have hpqpnnp: (((P → Q) → P) → ¬¬P) := peirce_law_weak P Q
  have notnotp: ¬¬P := hpqpnnp hpqp
  have hnnpp: (¬¬P → P) := doubleneg_elim P
  exact hnnpp notnotp

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  := by
  intro hpq
  intro hnpnq
  apply Or.elim hpq
  intro p
  exact And.left hnpnq p
  intro q
  exact And.right hnpnq q

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  := by
  intro hpq
  intro hnpnq
  apply Or.elim hnpnq
  intro notp
  exact notp (And.left hpq)
  intro notq
  exact notq (And.right hpq)

------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := by
  intro nhpq
  apply And.intro
  intro p
  suffices hpq: (P∨Q) from nhpq hpq
  apply Or.inl
  exact p
  intro q
  suffices hpq': (P∨Q) from nhpq hpq'
  apply Or.inr
  exact q

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  := by
  intro hnpnq
  intro hpq
  apply Or.elim hpq
  intro p
  exact And.left hnpnq p
  intro q
  apply And.right hnpnq q

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  := by 
  intro nhpq
  by_cases p: P
  apply Or.inl
  intro q
  suffices hpq: (P∧Q) from nhpq hpq
  apply And.intro
  exact p
  exact q
  apply Or.inr
  exact p

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  := by
  intro hnqnp
  intro hpq
  apply Or.elim hnqnp
  intro notq
  exact notq (And.right hpq)
  intro notp
  exact notp (And.left hpq)

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  := by
  apply Iff.intro
  exact demorgan_conj P Q
  exact demorgan_conj_converse P Q

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  := by
  apply Iff.intro
  exact demorgan_disj P Q
  exact demorgan_disj_converse P Q

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  := by
  intro hpqr
  apply Or.elim (And.right hpqr)
  intro q
  apply Or.inl
  apply And.intro
  exact And.left hpqr
  exact q
  intro r
  apply Or.inr
  apply And.intro
  exact And.left hpqr
  exact r

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  := by
  intro hpqpr
  apply Or.elim hpqpr
  intro hpq
  apply And.intro
  exact And.left hpq
  apply Or.inl
  exact And.right hpq
  intro hpr
  apply And.intro
  exact And.left hpr
  apply Or.inr
  exact And.right hpr

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  := by
  intro hpqr
  apply Or.elim hpqr
  intro p
  apply And.intro
  apply Or.inl
  exact p
  apply Or.inl
  exact p
  intro hqr
  apply And.intro
  apply Or.inr
  exact And.left hqr
  apply Or.inr
  exact And.right hqr

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  := by
  intro hpqpr
  apply Or.elim (And.left hpqpr)
  intro p
  apply Or.inl
  exact p
  intro q
  apply Or.elim (And.right hpqpr)
  intro p
  apply Or.inl
  exact p
  intro r
  apply Or.inr
  apply And.intro
  exact q
  exact r

------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  := by
  intro hpqr
  intro p
  intro q
  suffices hpq: (P∧Q) from hpqr hpq
  apply And.intro
  exact p
  exact q

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  := by
  intro hpqr
  intro hpq
  have hqr: (Q→R) := hpqr (And.left hpq)
  exact hqr (And.right hpq)

------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  := by
  intro p
  apply Or.inl
  exact p

theorem weaken_disj_left :
  Q → (P∨Q)  := by
  intro q
  apply Or.inr
  exact q

theorem weaken_conj_right :
  (P∧Q) → P  := by
  intro hpq
  exact And.left hpq

theorem weaken_conj_left :
  (P∧Q) → Q  := by
  intro hpq
  exact And.right hpq

theorem conj_idempot :
  (P∧P) ↔ P := by
  apply Iff.intro
  exact weaken_conj_right P P
  intro p
  apply And.intro
  exact p
  exact p

theorem disj_idempot :
  (P∨P) ↔ P  := by
  apply Iff.intro
  intro hpp
  apply Or.elim hpp
  exact impl_refl P
  exact impl_refl P
  exact weaken_disj_left P P

end propositional


----------------------------------------------------------------


section predicate

variable (U : Type)
variable (P Q : U -> Prop)


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  := by
  intro hne
  intro x
  intro p
  suffices he: (∃x, P x) from hne he
  apply Exists.intro x p

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  := by
  intro han
  intro he
  apply Exists.elim he
  intro x
  intro px
  have npx: ¬P x := han x
  exact npx px

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  := by sorry

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  := by
  intro hen
  intro ha
  apply Exists.elim hen
  intro x npx
  have px: P x := ha x
  exact npx px

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  := by sorry

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
