import Lib.Adelic.Unitary.Defs
import Lib.General.Analysis.FiniteFourier
import Lib.General.LinearAlgebra.IntegralLattices

/-!
# Functions of positive type and singular minors

A function `Θ` on a finite group `G` is of positive type if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for some
vectors `u a` of a complex inner product space.

Notions from other files:

* `New.invTransposeGL` is the automorphism `g ↦ (gᵀ)⁻¹` of `GL n R`.

## Main definitions and results

* `New.card_mul_sum_det_eq_zero_le`: let `k` be a field with `q` elements, `π` a representation by
  `n × n` matrices over `k`, `A₀` and `A₁` two `n × m` matrices and `Θ ≥ 0` of positive type.
  Suppose that, for `v ≠ 0`, the stabilisers of `A₀ v` under `π` and of `A₁ v` under the
  contragredient of `π` have `Θ`-mass at most `Y ≥ 0`. Then the set where `det (A₁ᵀ π(s) A₀)`
  vanishes has mass at most `(2 Θ(G) + q ^ (|m| + |n| / 2) Y) / q`. The proof counts the kernel with
  an additive character and uses Cauchy–Schwarz.

## Relation to the literature

See `New.Spanning.Unfolding.Moments` for related work.
-/

open scoped BigOperators
open InnerProductSpace Finset EuclideanSpace Complex Matrix WithLp Fintype AddChar

namespace New

variable {G H k n m : Type*} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Field k] [Fintype n] [DecidableEq n] [Fintype m] {u : G → H}

/-- If the inner product of two families of vectors indexed by a finite group `G` has the form
`⟪u a, v b⟫ = f (a⁻¹ * b)`, then `⟪∑ a, u a, ∑ a, v a⟫ = |G| · ∑ s, f s`. -/
lemma inner_sum_sum_eq_card_mul {v : G → H} (f : G → ℂ)
    (h : ∀ a b : G, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) :
    ⟪∑ a : G, u a, ∑ a : G, v a⟫_ℂ = Fintype.card G * ∑ s : G, f s := by
  simp [↓sum_inner, inner_sum, h, (Group.mulLeft_bijective _).sum_comp]

/-- Let `π` be a representation of a finite group `G` by `n × n` matrices over a field with `q`
elements, and let `π' s` be the inverse transpose of `π s`. Let `A₀` and `A₁` be two `n × m`
matrices, and let `Θ ≥ 0` be of positive type: `Θ (a⁻¹ * b) = ⟪u a, u b⟫`. Suppose that, for every
`v ≠ 0`, each of two sums of `Θ` is at most `Y ≥ 0`: the sum over the `s` with `π s` fixing `A₀ v`,
and the sum over the `s` with `π' s` fixing `A₁ v`. Then `q · Θ {s | det (A₁ᵀ π(s) A₀) = 0} ≤ 2
Θ(G) + q ^ (|m| + |n| / 2) Y`. -/
lemma card_mul_sum_det_eq_zero_le [DecidableEq m] [Fintype k] [DecidableEq k] (π : G →* GL n k)
    (A₀ A₁ : Matrix n m k) {Θ : G → ℝ} (hΘ : ∀ s : G, 0 ≤ Θ s)
    (hu : ∀ a b : G, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) (Y : ℝ) (hY : 0 ≤ Y)
    (h_fix₀ : ∀ v : m → k, v ≠ 0 → ∑ s : G with A₀ *ᵥ v = π s • A₀ *ᵥ v, Θ s ≤ Y)
    (h_fix₁ : ∀ v : m → k, v ≠ 0 → ∑ s : G with A₁ *ᵥ v = invTransposeGL (π s) • A₁ *ᵥ v, Θ s ≤ Y) :
    Fintype.card k * ∑ s : G with (A₁ᵀ * (π s).val * A₀).det = 0, Θ s ≤
      2 * ∑ s : G, Θ s +
        Fintype.card k ^ Fintype.card m * √(Fintype.card k ^ Fintype.card n) * Y := by
  classical
  let A : Bool → Matrix n m k := fun b ↦ cond b A₁ A₀
  have h (b : Bool) (v : m → k) (hv : v ≠ 0) :
      ∑ s : G with A b *ᵥ v = cond b invTransposeGL 1 (π s) • A b *ᵥ v, Θ s ≤ Y := by
    cases b
    · simpa [A] using h_fix₀ v hv
    · simpa [A] using h_fix₁ v hv
  change card k * ∑ s with ((A true)ᵀ * (π s).val * A false).det = 0, Θ s ≤ _
  set r := √_
  obtain ⟨ψ, p⟩ : ∃ _, _ := ⟨_, FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  have N {c : (n → k) → EuclideanSpace ℂ (n → k)} (h : Orthonormal ℂ c) {σ : MulAut _} x :
      ∑ s with x = σ (π s) • x, Θ s = ‖∑ a, c (σ (π a) • x) ⊗ₜ[ℂ] u a‖ ^ 2 / card G
  rw [@norm_sq_eq_re_inner ℂ, inner_sum_sum_eq_card_mul (ofReal ∘ _)]
  simpa using sum_filter ..
  simp [*, orthonormal_iff_ite.1, apply_ite ofReal, mul_smul, eq_inv_smul_iff]
  let W y v s := ψ (y ᵥ* (A true)ᵀ ᵥ* π s ᵥ* A false ⬝ᵥ v) * Θ s
  apply ((sum_mono fun y ↦ univ.expect_le_expect fun v _ ↦ (?_ : re (∑ s, W y v s) ≤
    ite (y = 0) (∑ s, Θ s) 0 + ite (v = 0) (∑ s, Θ s) 0 + r * Y)).trans _).trans'
  simp [W, -ite_mul, sum_comm, mul_sum, sum_filter, apply_ite, ↓← re_expect, ← sum_mul, ← mul_assoc,
    expect, NNRat.smul_def, sum_addChar_dotProduct p]
  gcongr; repeat' split
  cases exists_vecMul_eq_zero_iff.2 ‹_›
  grw [← card_univ, card_le_card_of_injOn _ _ (smul_left_injective _ (by tauto)).injOn]
  on_goal -1 => apply flip id (add_le_add (h true y _) (h false v _))
                grw [@N fun x ↦ toLp 2 fun ζ ↦ ψ (-x ⬝ᵥ ζ) / r, N orthonormal_single, ← add_div,
    ← two_mul_le_add_sq, mul_assoc, ← @re_inner_le_norm ℂ, inner_sum_sum_eq_card_mul (W y v · / r)]
  all_goals simp [sum_add_distrib, sub_eq_zero, *, smul_vecMul, mul_nonneg, expect_add_distrib,
    NNRat.smul_def, W, r, add_nonneg,
    sum_nonneg', inner, field, vecMul_mulVec, ← Matrix.mul_assoc, orthonormal_iff_ite, two_mul,
    invTransposeGL, dotProduct_mulVec, div_mul_div_comm, ← map_neg_eq_conj, ← map_add_eq_mul,
    ← ofReal_mul, transposeGL,
    add_assoc, ← sum_div, neg_add_eq_sub, ← sub_dotProduct, sum_addChar_dotProduct, Units.smul_def]

end New
