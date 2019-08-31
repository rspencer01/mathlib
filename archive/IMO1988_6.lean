/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
-/
import data.int.basic
/-!
IMO Problem 1988-6.
Let `a` and `b` be positive integers such that `ab + 1` divides `a^2 + b^2`. Show that
```
(a^2 + b^2) / (ab + 1)
```
is the square of an integer.
-/

/-- We first prove a reformulation of the problem. -/
theorem IMO1988_6_aux (k : ℕ) (h : ∃ a b : ℕ, a * a + b * b = (a * b + 1) * k) :
  ∃ l : ℕ , l * l = k :=
begin
  have lemma1 : ∀{a b : ℤ}, a * a + b * b = (a * b + 1) * k ↔ b * b - (k * a) * b + (a * a - k) = 0,
  { intros, rw [right_distrib, ← sub_eq_iff_eq_add, ← sub_eq_zero], simp [mul_comm, mul_assoc] },
  cases nat.eq_zero_or_pos k with hk hk, { use 0, rw [hk], refl }, -- for `k = 0` we are done
  -- `s` is the set of `(a,b)` where `a^2 + b^2 = (ab + 1) * k`
  let s : set (ℕ × ℕ) := { ab | ab.1 * ab.1 + ab.2 * ab.2 = (ab.1 * ab.2 + 1) * k },
  have hs : s ≠ ∅, -- it is non-empty
  { rw [set.ne_empty_iff_exists_mem], rcases h with ⟨a, b, hab⟩, use ⟨a, b⟩, simp [hab] },
  /- We now find a solution `(a, b)` where `a + b` is minimal and `a ≤ b`. -/
  let r : ℕ × ℕ → ℕ := λ ab, ab.1 + ab.2,
  let s_min := well_founded.min (measure_wf r) s hs,
  let a' : ℕ := min s_min.1 s_min.2,
  let b' : ℕ := max s_min.1 s_min.2,
  let a : ℤ := a',
  let b : ℤ := b',
  have ha : 0 ≤ a := int.coe_zero_le a',
  have hb : 0 ≤ b := int.coe_zero_le b',
  have a_le_b : a ≤ b, { apply_mod_cast min_le_max },
  have hab : a * a + b * b = (a * b + 1) * k,
  { norm_cast,
    rw [fn_min_add_fn_max (λ x, x * x) s_min.1 s_min.2, min_mul_max s_min.1 s_min.2],
    exact well_founded.min_mem (measure_wf r) s hs },
  have h2ab : b * b - (k * a) * b + (a * a - k) = 0, { rwa [← lemma1] },
  cases eq_or_lt_of_le ha with h2a h2a, -- if `a = 0` then `k = b ^ 2` and we are done
  { use b', rw [← h2a] at hab, have : b * b = k, { simpa using hab }, exact_mod_cast this },
  /- Let `c : ℤ` be the other solution to the quadratic equation.
    By the rules between roots and coefficients we have `b + c = ak` and bc = `a^2 - k` -/
  rcases Vieta_formula_quadratic h2ab with ⟨c, h1c, h2c, h3c⟩,
  have h4c : c ≥ 0,
  { have h1 : a * a + c * c = (a * c + 1) * k, -- now `(a,c)` is a solution
    { rwa [lemma1] },
    have : 0 ≤ (a * c + 1) * k,
    { rw [← h1], apply add_nonneg; apply mul_self_nonneg },
    have : 0 ≤ a * c + 1,
    { apply nonneg_of_mul_nonneg_right this, apply_mod_cast hk },
    have : 0 ≤ a * c, /- if `ac + 1 = 0` then `a = c = 0` by `h1`, but we assumed that `a > 0` -/
    { apply int.le_of_lt_add_one, apply lt_of_le_of_ne this,
      intro h2, rw [← h2, zero_mul, mul_self_add_mul_self_eq_zero] at h1,
      exact ne_of_gt h2a h1.1 },
    exact nonneg_of_mul_nonneg_left this h2a }, -- So `c ≥ 0`
  have h5c : c < b, -- Now `c < b` since `bc = a^2 - k < a^2 ≤ b^2`
  { apply lt_of_mul_lt_mul_left _ hb, rw [h3c],
    apply lt_of_lt_of_le (sub_lt_self _ _) (mul_le_mul a_le_b a_le_b ha hb),
    apply_mod_cast hk },
  lift c to ℕ using h4c, -- we treat `c` as a natural number
  have h6c : (a', c) ∈ s, -- now `(a, c)` is also a solution
  { rw [← lemma1] at h1c, exact_mod_cast h1c },
  have : a' + b' ≤ a' + c, -- so it cannot be smaller than the smallest solution
  { rw [← not_lt, min_add_max s_min.1 s_min.2],
    exact well_founded.not_lt_min (measure_wf r) s hs h6c },
  exfalso, apply not_le_of_lt h5c, -- but `c < b`, contradiction.
  apply_mod_cast le_of_add_le_add_left this
end

/- From this it is easy to prove the actual problem. -/
theorem IMO1988_6 (a b : ℕ) (h : a*b + 1 ∣ a^2 + b^2) : ∃ k : ℕ , k^2 = (a^2 + b^2) / (a * b + 1) :=
begin
  cases h with k hk,
  cases IMO1988_6_aux k ⟨a, b, _⟩ with l hl,
  swap, rw [← nat.pow_two, ← nat.pow_two, hk],
  use l, rw [hk, nat.mul_div_cancel_left], rw [nat.pow_two, hl], apply nat.zero_lt_succ
end
