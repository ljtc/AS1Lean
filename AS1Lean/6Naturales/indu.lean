import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

variable (α : Type*) (s : Finset ℕ)

open Finset
open Nat


/-
# Inducción
El esquema de inducción requiere una fórmula φ(x). Con ella
podemos escribir inducción en ℕ como sigue:
φ(0) ∧ (∀ n, φ(n) → φ(n+1)) → ∀ n, φ(n).
Así, una demostración por inducción está dividida en tres partes:
1. Base de inducción: mostrar que el mínimo satisface la fórmula, φ(0)
2. Hipótesis de inducción: suponer que n satisface, φ(n)
3. Paso inductivo: demostrar que n + 1 satisface, φ(n + 1).
Cuando se hayan realizado estos tres pasos, el esquema de inducción
nos permite concluir ∀ n, φ(n).
-/

--La suma de los primeros n números
example (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm
  apply Nat.div_eq_of_eq_mul_right
  · norm_num
  · induction' n with n HI
    · rw [zero_mul, sum_range_succ, sum_range_zero, add_zero, mul_zero]
      --funciona sólo escribir la táctica `simp`
    · rw [sum_range_succ, mul_add 2, <-HI]
      rw [<-add_mul, mul_comm]
      --funciona sólo escribir la táctica `ring`


--La suma de los primeros n cuadrados
example (n : ℕ) : ∑ i ∈ range (n + 1),
                  i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right
  · norm_num
  · induction' n with n HI
    · rw [zero_mul, zero_mul]
      rw [sum_range_one, pow_two, mul_zero, mul_zero]
    · rw [sum_range_succ, mul_add 6, <-HI]
      ring


/-
# Inducción fuerte
El esquema de inducción fuerte en ℕ considera una fórmula φ(x).
Con ella el enunciado es
∀ n, (∀ m < n, φ(m) → φ(n)) → ∀ n, φ(n).
Este método no requiere un base. La hipótesis de inducción es que
todos los números menores que n satisfacen φ y el paso inductivo
consiste en mostrar que n también satisface φ.
-/


--Todo número mayor o igual a 2 tiene un factor primo
example (n : ℕ)(h: 2 ≤ n) : ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n
  · induction' n using Nat.strong_induction_on with n HI
    rw [prime_def_lt] at np
    push_neg at np
    obtain ⟨m, mlen, mdn, mne1⟩ := np h
    have mne0 : m ≠ 0 := by
      intro m0
      rw [m0, zero_dvd_iff] at mdn
      linarith
    have mg2 : 2 ≤ m := by
      apply (two_le_iff m).mpr
      exact ⟨mne0, mne1⟩
    by_cases mp : m.Prime
    · use m
    · obtain ⟨p, pp, pdm⟩ := HI m mlen mg2 mp
      use p
      constructor
      · assumption
      · apply dvd_trans pdm mdn
