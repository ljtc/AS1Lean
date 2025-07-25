import Mathlib.Tactic

variable (α : Type) (p q : α → Prop)
variable (c r : Prop)

/-
# Lógica de primer orden
-/

/-
## Donde la variable cuantificada no aparece
-/
example (a : α) : (∃ x : α, c) ↔ c := by
  constructor
  · intro ⟨_, hc⟩
    assumption
  · intro hc
    exact ⟨a, hc⟩

example (a : α) : (∀ x : α, r) ↔ r := by
  constructor
  · intro h
    exact h a
  · intro hr _
    assumption


/-
## Comportamioento con la conjunción
-/

-- ∀ con ∧
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h
    constructor
    · intro a
      exact (h a).1
    · intro a
      exact (h a).2
  · intro ⟨h, h'⟩ x
    exact ⟨h x, h' x⟩

-- ∃ con ∧
-- sólo se vale una implicación
example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := by
  intro ⟨a, ⟨pa, qa⟩⟩
  constructor
  · exact ⟨a, pa⟩
  · exact ⟨a, qa⟩

--consecuencia de lo anterior
example (a : α) : (∀ x, p x ∧ c) ↔ (∀ x, p x) ∧ c := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1
    · exact (h a).2
  · intro h x
    exact ⟨(h.1) x, h.2⟩

-- caso especial con ∃ y ∧
example : (∃ x, p x ∧ c) ↔ (∃ x, p x) ∧ c := by
  constructor
  · intro ⟨a, h⟩
    constructor
    · use a
      exact h.1
    · exact h.2
  · intro ⟨⟨a, hp⟩, hc⟩
    exact ⟨a, ⟨hp, hc⟩⟩


/-
## Comportamiento con la disyunción
-/

-- ∀ con ∨
-- sólo se vale una implicación
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h a
  rcases h with hp | hq
  · left
    exact hp a
  · right
    exact hq a

-- ∃ con ∨
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro ⟨a, hpq⟩
    rcases hpq with hp | hq
    · left
      exact ⟨a, hp⟩
    · right
      exact ⟨a, hq⟩
  · intro h
    rcases h with ⟨a, hp⟩ | ⟨a, hq⟩
    · exact ⟨a, Or.inl hp⟩
    · use a
      right
      assumption

-- consecuencioa de lo anterior
example (a : α) : (∃ x, p x ∨ c) ↔ (∃ x, p x) ∨ c := by
  constructor
  · rintro ⟨b, (pb | hc)⟩
    · left
      exact ⟨b, pb⟩
    · right
      assumption
  · rintro (⟨b, pb⟩ | hc)
    · use b
      left
      assumption
    · use a
      right
      assumption

-- caso especial
example : (∀ x, p x ∨ c) ↔ (∀ x, p x) ∨ c := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    rcases h'.1 with ⟨a, hnp⟩
    rcases (h a) with hp | hc
    · exact hnp hp
    · exact h'.2 hc
  · intro h a
    rcases h with hp | _
    · left
      exact hp a
    · right
      assumption


/-
## Comportamiento con la implicación
-/

-- ∀ con →
-- sólo se vale una implicación
example : (∀ x, p x → q x) → ((∀ x, p x) → (∀ x, q x)) := by
  intro h h' a
  exact (h a) (h' a)


-- caso especial, consecuente
example : (∀ x, p x → c) ↔ (∃ x, p x) → c := by
  constructor
  · intro h ⟨a, hp⟩
    exact (h a) hp
  · intro h a hp
    exact h ⟨a, hp⟩

example (a : α) : (∃ x, p x → c) ↔ (∀ x, p x) → c := by
  constructor
  · intro ⟨b, hpr⟩ h
    exact hpr (h b)
  · intro h
    by_contra h'
    push_neg at h'
    have : ∀ (x : α), p x := by
      intro b
      exact (h' b).1
    exact (h' a).2 (h this)

-- caso especial, antecedente
example (a : α) : (∃ x, c → p x) ↔ (c → ∃ x, p x) := by
  constructor
  · intro ⟨b, hrp⟩ hc
    use b
    apply hrp
    exact hc
  · intro h
    by_contra! h'
    have : ∃ x, p x := by
      apply h
      exact (h' a).1
    obtain ⟨b, hb⟩ := this
    exact (h' b).2 hb


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  · intro h hr a
    exact (h a) hr
  · intro h a hr
    exact (h hr) a


/-
## Comportamiento con la negación
-/
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · intro h ⟨a, hnp⟩
    exact hnp (h a)
  · intro h a
    push_neg at h
    exact h a

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  · intro ⟨a, hp⟩ h
    exact (h a) hp
  · intro h
    push_neg at h
    assumption

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  · intro h a
    push_neg at h
    exact h a
  · intro h ⟨a, hp⟩
    exact (h a) hp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  · intro h
    push_neg at h
    assumption
  · intro ⟨a, hnp⟩ h
    exact hnp (h a)
