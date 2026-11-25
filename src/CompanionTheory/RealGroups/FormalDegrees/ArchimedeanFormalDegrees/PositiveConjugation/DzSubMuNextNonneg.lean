module

import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.DzSubMuNextNonneg
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Minors
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inP_entry_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n}
    (h : ε a = ε b) : X a b = 0 := by
  have h1 := congrFun (congrFun hX.2 a) b
  simp only [Matrix.mul_apply, Matrix.neg_apply, Jm, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  rw [h] at h1
  split_ifs at h1 with hb
  · have : (2 : ℂ) * X a b = 0 := by linear_combination h1
    simpa using this
  · have : (2 : ℂ) * X a b = 0 := by linear_combination -h1
    simpa using this

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  apply PositivityTheory.RgFd.exists_pmat <;> assumption

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, rfl⟩ := exists_pmat hX
  have h0 := fi_nonneg z i
  have hp := (lead_posDef (exp_noncompactPart_posDef hX) i hi).1
  unfold Fi at h0
  have e : Del (NormedSpace.exp (pmat z)) i = lead i (NormedSpace.exp (pmat z)) := rfl
  rw [e] at h0
  exact (Real.log_nonneg_iff hp).1 h0

theorem dz_sub_muNext_nonneg (i : Fin n) : 0 ≤ Dz n i - muNext (Dz n) i := by
  unfold muNext Dz
  split_ifs with h
  · simp only
    omega
  · have : (i : ℕ) + 1 = n := by omega
    omega

theorem phiLe : PhiLe :=
  _root_.PositivityTheory.RgFd.phiLe

end CompanionTheory.RgFd
