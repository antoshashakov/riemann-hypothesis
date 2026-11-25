module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.TransvectionIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GaussTailOfCardLe

@[expose] public section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset MeasureTheory Filter Topology Set

private theorem pow_le_pow_left_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  exact pow_le_pow_left₀ hx hxy n

theorem ballVolume : BallVolume := by
  intro D rr hr
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr) = _
    have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr = Set.univ := by
      ext z
      simp only [mem_ball_zero_iff, Set.mem_univ, iff_true]
      have hz : ‖z‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [hz]
      exact hr
    have hpar : parallelepiped (EuclideanSpace.basisFun (Fin 0) ℝ) = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      have hz : z = 0 := by
        rw [← norm_eq_zero, EuclideanSpace.norm_eq]
        simp
      rw [hz, mem_parallelepiped_iff]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    rw [hb, ← hpar, OrthonormalBasis.volume_parallelepiped]
    simp
  have : Nonempty (Fin (2 * D)) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have hg : Real.Gamma (((2 * D : ℕ) : ℝ) / 2 + 1) = (D.factorial : ℝ) := by
    rw [show ((2 * D : ℕ) : ℝ) / 2 + 1 = (D : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial D
  have hs : Real.sqrt Real.pi ^ (2 * D) = Real.pi ^ D := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hg, hs, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem exp_neg_sq_div_sixteen_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-t ^ 2 / 16) ≤ Real.exp (-s ^ 2 / 16) :=
  Real.exp_le_exp.mpr (by nlinarith)

private theorem gaussian_tail_pow_mul_exp_le {g : ℕ} {R0 s t : ℝ} (hR0 : 0 < R0)
    (hg : 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2) (hs : R0 ≤ s) (hst : s ≤ t) :
    (2 * (3 * t / R0) ^ (2 * g) - (3 * s / R0) ^ (2 * g)) * Real.exp (-t ^ 2 / 16) ≤
      (3 * s / R0) ^ (2 * g) * Real.exp (-s ^ 2 / 16) := by
  have hs0 : 0 < s := lt_of_lt_of_le hR0 hs
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (t ^ 2 - s ^ 2) / 16 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (u / 2) := ⟨_, rfl⟩
  have hE2 : E ^ 2 = Real.exp u := by
    rw [show E ^ 2 = E * E by ring, hE, ← Real.exp_add]
    congr 1
    ring
  have hfs : Real.exp (-s ^ 2 / 16) = Real.exp (-t ^ 2 / 16) * E ^ 2 := by
    rw [hE2, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  have hK : 0 < 2 * (g : ℝ) + 1 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u / (2 * (g : ℝ) + 1) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg hu0 hK.le
  have hvK : v * (2 * (g : ℝ) + 1) = u := by rw [hv]; field_simp
  have hR2 : R0 ^ 2 ≤ s ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ s ^ 2 * (1 + v) := by
    have h16 : 16 * (2 * (g : ℝ) + 1) ≤ s ^ 2 := le_trans hg hR2
    have htu : t ^ 2 = s ^ 2 + 16 * u := by rw [hu]; ring
    nlinarith [mul_le_mul_of_nonneg_left h16 hv0]
  have hP : ∀ x : ℝ, (3 * x / R0) ^ (2 * g) = ((3 / R0) ^ 2 * x ^ 2) ^ g := by
    intro x
    rw [pow_mul]
    congr 1
    ring
  have hBt : (3 * t / R0) ^ (2 * g) ≤ (3 * s / R0) ^ (2 * g) * E := by
    rw [hP t, hP s]
    have h1 : (3 / R0) ^ 2 * t ^ 2 ≤ ((3 / R0) ^ 2 * s ^ 2) * (1 + v) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
    have h2 : ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g :=
      pow_le_pow_left_of_nonneg (by positivity) h1 g
    have h3 : (1 + v) ^ g ≤ E := by
      have hexp : (1 + v) ^ g ≤ (Real.exp v) ^ g :=
        pow_le_pow_left_of_nonneg (by linarith) (by linarith [Real.add_one_le_exp v]) g
      have hnat : (Real.exp v) ^ g = Real.exp (g * v) := by
        exact (Real.exp_natCast_mul g v).symm
      have hle : Real.exp (g * v) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    calc ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g := h2
      _ = ((3 / R0) ^ 2 * s ^ 2) ^ g * (1 + v) ^ g := mul_pow _ _ _
      _ ≤ ((3 / R0) ^ 2 * s ^ 2) ^ g * E := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hft : 0 ≤ Real.exp (-t ^ 2 / 16) := (Real.exp_pos _).le
  have hBs : 0 ≤ (3 * s / R0) ^ (2 * g) := by rw [hP s]; positivity
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_right hBt hft, mul_nonneg (mul_nonneg hBs hft) (sq_nonneg (E - 1))]

theorem gaussian_tail_bound : GaussianTailBound :=
  _root_.GlobalTheory.gaussTail_of_card_le

end Formalism.LatticeBaseChangeAlt
