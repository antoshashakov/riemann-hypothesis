module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem _root_.UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (eD : R), Function.Bijective (act eD) → ∀ (F : ℤ → W → Prop), (∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : ℕ) (h b : ι → W) (m m' : Matrix ι ι R), m' * m = 1 → (∀ i, h i = ∑ k, act (eD ^ β * m i k) (b k)) → (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k)) → ∀ w, F (β : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i) := by
  intro R W _ _ act hmul hone eD hbij F hF ι _ _ β h b m m' hm hh hF0 w
  let ψ : R →* Function.End W :=
    { toFun := fun r w => act r w, map_one' := funext hone,
      map_mul' := fun r s => funext (hmul r s) }
  have hmain : ∀ (n : ℕ) (y : W), F 0 y ↔ F n (act (eD ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; simp [hone]
    | succ n ih =>
      intro y
      simpa [Nat.cast_succ, pow_succ', hmul] using (ih y).trans (hF (act (eD ^ n) y) ↑n)
  have hbij' : Function.Bijective (act (eD ^ β)) := by
    rw [show ⇑(act (eD ^ β)) = (act eD)^[β] from map_pow ψ eD β]
    exact hbij.iterate β
  have hexp : ∀ e : ι → R,
      ∑ i, act (e i) (h i) = act (eD ^ β) (∑ k, act (Matrix.vecMul e m k) (b k)) := by
    intro e
    simp only [hh, map_sum, AddMonoidHom.finsetSum_apply, ← hmul, Matrix.vecMul_apply_eq_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨y, rfl⟩ := hbij'.2 w
  rw [← hmain β y, hF0]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨Matrix.vecMul d m', ?_⟩
    simp only [hexp, Matrix.vecMul_vecMul, hm, Matrix.vecMul_one, hd]
  · rintro ⟨e, he⟩
    exact ⟨Matrix.vecMul e m, hbij'.1 (by rw [he, hexp])⟩
