
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_contra destructionandtears,
  apply hp,
  exact destructionandtears,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro hp,
  by_contra destructionandtears,
  apply hp,
  exact destructionandtears,
  intro hp,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro blood,
  cases blood with sweat tears,
  right,
  exact sweat,
  left,
  exact tears,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hp,
  split,
  cases hp with h1 h2,
  exact h2,
  cases hp with h1 h2,
  exact h1,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro verge,
  intro hp2,
  cases verge with of tears,
  contradiction,
  exact tears,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro the,
  intro skip,
  cases the with good part,
  contradiction,
  exact part,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro thehouse,
  intro ajr,
  intro down,
  have burn : Q := thehouse down,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro bummer,
  intro pop,
  by_contra land,
  have ajr : ¬P := bummer land,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro hp,
  intro hp2,
  intro hp3,
  have hp4 : Q := hp hp3,
  contradiction,
  intro bummer,
  intro pop,
  by_contra land,
  have ajr : ¬P := bummer land,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hp,
  have h : P∨¬P,
  right,
  intro hp2,
  have i : P∨¬P,
  left,
  exact hp2,
  contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hp,
  intro hp2,
  have hp3 : ¬P∨Q,
  left,
  exact hp2,
  have hp4 : P→Q,
  intro hp5,
  contradiction,
  have hp6 : P := hp hp4,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro way,
  intro the,
  cases way with less sad,
  cases the with good part,
  contradiction,
  cases the with entertainment ishere,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro Christmas,
  intro Bang,
  cases Christmas with In June,
  cases Bang with I won't,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro Netflix,
  split,
  intro Trip,
  have Karma : P∨Q,
  left,
  exact Trip,
  contradiction,
  intro Trip,
  have Joe : P∨Q,
  right,
  exact Trip,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro Indie,
  intro next,
  cases Indie with my play,
  cases next with up forever,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hp,
  by_cases hp2 : P,
  left,
  intro hp3,
  have hp4 : P∧Q,
  split,
  exact hp2,
  exact hp3,
  contradiction,
  right, 
  exact hp2,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro Ok,
  intro Orchestra,
  cases Orchestra with Sober Up,
  cases Ok with Birthday Party,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro hp,
  by_cases hp2 : P,
  left,
  intro hp3,
  have hp4 : P∧Q,
  split,
  exact hp2,
  exact hp3,
  contradiction,
  right, 
  exact hp2,
  intro Ok,
  intro Orchestra,
  cases Orchestra with Sober Up,
  cases Ok with Birthday Party,
  contradiction,
  contradiction,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro Netflix,
  split,
  intro Trip,
  have Karma : P∨Q,
  left,
  exact Trip,
  contradiction,
  intro Trip,
  have Joe : P∨Q,
  right,
  exact Trip,
  contradiction,
  intro Indie,
  intro next,
  cases Indie with my play,
  cases next with up forever,
  contradiction,
  contradiction,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro Adventure,
  cases Adventure with isOut There,
  cases There with Ordinaryish People,
  left,
  split,
  exact isOut,
  exact Ordinaryish,
  right,
  split,
  exact isOut,
  exact People,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro Don't,
  cases Don't with Throw Out,
  cases Throw with My Legos,
  split,
  exact My,
  left,
  exact Legos,
  cases Out with Normal Drama,
  split,
  exact Normal,
  right,
  exact Drama,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro Weak,
  split,
  cases Weak with Thirty Three,
  left,
  exact Thirty,
  right,
  cases Three with O'clock Things,
  exact O'clock,
  cases Weak with Trick The,
  left,
  exact Trick,
  right,
  cases The with Good Part,
  exact Part,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro Wow,
  cases Wow with I'm NotCrazy,
  cases I'm with a Believer,
  left,
  exact a,
  cases NotCrazy with Pitchfork Kids,
  left,
  exact Pitchfork,
  right,
  split,
  exact Believer,
  exact Kids,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro hp,
  intro hp2,
  intro hp3,
  have hp4: P∧Q,
  split,
  exact hp2,
  exact hp3,
  have hp5: R := hp hp4,
  exact hp5,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hp,
  intro hp2,
  cases hp2 with hp3 hp4,
  have hp5 : Q→R := hp hp3,
  have hp6 : R := hp5 hp4,
  exact hp6,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h,
  exact h,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hp,
  right,
  exact hp,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro world's,
  cases world's with smallest violin,
  exact smallest,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro ajr,
  cases ajr with bummer land,
  exact bummer,
  intro pop,
  split,
  exact pop,
  exact pop,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro come,
  cases come with hang out,
  exact hang,
  exact out,
  intro ajr,
  left,
  exact ajr,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hp,
  intro a,
  intro boom,
  apply hp,
  existsi a,
  exact boom,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hp,
  intro hp2,
  cases hp2 with a ha,
  apply hp,
  exact ha,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hp,
  by_contra cry,
  have more: ∀x, P x,
  intro a,
  by_contra boom,
  have hp2 : ∃x, ¬P x,
  existsi a,
  exact boom,
  contradiction,
  contradiction,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hp,
  intro hp2,
  cases hp with a ha,
  have hp3 : P a := hp2 a,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro hp,
  by_contra cry,
  have more: ∀x, P x,
  intro a,
  by_contra boom,
  have hp2 : ∃x, ¬P x,
  existsi a,
  exact boom,
  contradiction,
  contradiction,
  intro hp,
  intro hp2,
  cases hp with a ha,
  have hp3 : P a := hp2 a,
  contradiction,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro hp,
  intro a,
  intro hp2,
  apply hp,
  existsi a,
  exact hp2,
  intro hp,
  intro hp2,
  cases hp2 with a ha,
  apply hp,
  exact ha,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hp,
  intro hp2,
  cases hp with a ha,
  apply hp2,
  exact ha,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hp,
  intro hp2,
  cases hp2 with a ha,
  have hp3 : P a := hp a,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hp,
  intro a,
  by_contra boom,
  have hp1 : ∃x, ¬P x,
  existsi a,
  exact boom,
  contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro hp,
  by_contra boom,
  have hp1 : ∀ (x : U), ¬P x,
  intro a,
  intro ha,
  have hp2 : ∃ (x : U), P x,
  existsi a,
  exact ha,
  contradiction,
  contradiction,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro hp,
  intro hp2,
  cases hp2 with a ha,
  have hp3 : P a := hp a,
  contradiction,
  intro hp,
  intro a,
  by_contra boom,
  have hp1 : ∃x, ¬P x,
  existsi a,
  exact boom,
  contradiction,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro hp,
  intro hp2,
  cases hp with a ha,
  apply hp2,
  exact ha,
  intro hp,
  by_contra boom,
  have hp1 : ∀ (x : U), ¬P x,
  intro a,
  intro ha,
  have hp2 : ∃ (x : U), P x,
  existsi a,
  exact ha,
  contradiction,
  contradiction,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro hp,
  cases hp with a ha,
  cases ha with hp1 hp2,
  split,
  existsi a,
  exact hp1,
  existsi a,
  exact hp2,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro hp,
  cases hp with a ha,
  cases ha with hp1 hp2,
  left,
  existsi a,
  exact hp1,
  right,
  existsi a,
  exact hp2,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro hp,
  cases hp with hp1 hp2,
  cases hp1 with a ha,
  existsi a,
  left,
  exact ha,
  cases hp2 with b hb,
  existsi b,
  right,
  exact hb,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hp,
  split,
  intro a,
  have hp1 : P a ∧ Q a := hp a,
  cases hp1 with ha hb,
  exact ha,
  intro b,
  have hp2 : P b ∧ Q b := hp b,
  cases hp2 with ha hb,
  exact hb,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hp,
  cases hp with hp1 hp2,
  intro a,
  split,
  have ha : P a := hp1 a,
  exact ha,
  have hb : Q a := hp2 a,
  exact hb,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hp,
  cases hp with hp1 hp2,
  intro a,
  left,
  have ha: P a := hp1 a,
  exact ha,
  intro b,
  right,
  have hb : Q b := hp2 b,
  exact hb,
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
