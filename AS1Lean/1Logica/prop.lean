import Mathlib.Tactic

section prop
variable (a b c : Prop)

/-
# Lógica de proposiciones

## Comportamiento estructural
Veremos que las proposiciones forman un álgebra de Boole.
Además de algunas propiedades en la misma línea.
-/

--conmutatividad de `∧` y `∨`
example : a ∧ b ↔ b ∧ a := by
  constructor
  · intro ⟨ha, hb⟩
    constructor <;> assumption
  · intro ⟨hb, ha⟩
    constructor <;> assumption


example : a ∨ b ↔ b ∨ a := by
  constructor
  · rintro (ha | hb)
    · right; assumption
    · left; assumption
  · rintro (hb | ha)
    · right; assumption
    · left; assumption

--asociatividad de ∧ y ∨
example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c := by
  constructor
  · intro ⟨ha, ⟨hb, hc⟩⟩
    exact ⟨⟨ha, hb⟩, hc⟩
  · intro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, ⟨hb, hc⟩⟩

example : a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c := by
  constructor
  · rintro (ha | (hb | hr))
    · left; left; assumption
    · left; right; assumption
    · right; assumption
  · rintro ((ha | hb) | hc)
    · left; assumption
    · right; left; assumption
    · right; right; assumption

--∧ y ∨ son idempotentes
example : a ∧ a ↔ a := by
  constructor
  · intro h
    exact h.1
  · intro ha
    exact ⟨ha, ha⟩

example : a ∨ a ↔ a := by
  constructor
  · rintro (ha | ha) <;> assumption
  · intro ha
    left; assumption

--absorciones
example : a ∧ (a ∨ b) ↔ a := by
  constructor
  · rintro ⟨ha, (h | _)⟩ <;> assumption
  · intro ha
    constructor
    · assumption
    · left; assumption

example : a ∨ (a ∧ b) ↔ a := by
  constructor
  · rintro (ha | ⟨ha, _⟩) <;> assumption
  · intro ha
    left
    assumption

--distributividades
example : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := by
  constructor
  · rintro ⟨ha, (hb | hc)⟩
    · left
      exact ⟨ha, hb⟩
    · right
      exact ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · constructor
      · assumption
      · left; assumption
    · constructor
      · assumption
      · right; assumption

example : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) := by
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · constructor
      repeat' left; assumption
    · constructor
      repeat' right; assumption
  · rintro ⟨(ha | hb), (hp | hc)⟩
    · left; assumption
    · left; assumption
    · left; assumption
    · right; exact ⟨hb, hc⟩

-- complemento
example : a ∧ ¬a ↔ False := by
  constructor
  · intro ⟨ha, hna⟩
    exact hna ha
  · intro h
    exfalso
    assumption

/-
Nota:
Esta parte del complemento tiene implicaciones fuertes acerca del
tipo de lógica que vamos a trabajar. Esto es, requiere que la lógica
sea clásica. En este caso, la táctica `by_cases` carga el
comportamiento clásico
-/
example : a ∨ ¬a ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    by_cases h : a
    · left; assumption
    · right; assumption




/-
## Métodos de demostración
-/

--contrapuesta
example : (a → b) ↔ (¬b → ¬a) := by
  constructor
  · intro h hnq ha
    exact hnq (h ha)
  · intro h ha
    by_cases hb : b
    · assumption
    · exfalso
      exact (h hb) ha

--contradicción
example : (¬a → False) → a := by
  by_cases ha : a
  · intro h
    assumption
  · intro h
    exfalso
    apply h ha

end prop
