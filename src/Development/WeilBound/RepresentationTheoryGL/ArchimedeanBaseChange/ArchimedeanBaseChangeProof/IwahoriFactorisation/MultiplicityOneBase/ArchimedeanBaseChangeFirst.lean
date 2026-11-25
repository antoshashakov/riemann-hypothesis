module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroups
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriTrivialCase.IwahoriTrivialLemmas.UnitProductIndicatorTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first : PositivityTheory.Rg.Bc.ArchbcB.B.M1 := by
  intro E _ _ _ hE w hw n a b hab Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨K, e, he1, he2, he3, he4⟩ := _root_.GlobalTheory.InertUQ.exists_uq E hE w hw
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  obtain ⟨B₁, hg₁, hP₁, hst₁⟩ := _root_.GlobalTheory.InertTwUnit.twisted_unit_eq_stSum E hE w hw K e he1 he2 he3 he4 a Q₁ hm₁ hd₁ hs₁ hc₁
  obtain ⟨B₂, hg₂, hP₂, hst₂⟩ := _root_.GlobalTheory.InertTwUnit.twisted_unit_eq_stSum E hE w hw K e he1 he2 he3 he4 b Q₂ hm₂ hd₂ hs₂ hc₂
  have hk := _root_.GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum E hE w hw K e he1 he2 he3 he4 n Q₁ Q₂ hm₁ hm₂ (by omega) hsep hc₁ hc₂ B₁ B₂ hg₁ hg₂ hP₁ hP₂
  have hsepP : (B₁.P * B₂.P).Separable := by
    rw [hP₁, hP₂, ← Polynomial.map_mul]
    exact hsep.map
  have hid := _root_.GlobalTheory.UnitLemma.unitLemma_identity_unconditional K B₁ B₂ hg₁ hg₂ hsepP
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  have hv : GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) := by
    rw [he3, hP₁, hP₂]
    have h1 : (Q₁.map e.symm.toRingHom).natDegree = Q₁.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    have h2 : (Q₂.map e.symm.toRingHom).natDegree = Q₂.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    rw [h1, h2, Polynomial.resultant_map_map]
    simp
  rw [PositivityTheory.BcbA.Ties.unit_product_indicator_twist E hE a b w hw Q₁ Q₂ hs₁ hs₂, hst₁, hst₂, hk, ← Rat.cast_mul, ← hid, Rat.cast_mul]
  congr 1
  rw [hv]
  unfold delta absHalf
  rw [if_neg hw, he4]
  set v := ordL (resultant Q₁ Q₂)
  have hq : Real.sqrt (((K.q ^ 2 : ℕ) : ℝ) ^ (-v)) = (K.q : ℝ) ^ (-v) := by
    rw [Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    exact Real.sqrt_sq (zpow_nonneg (Nat.cast_nonneg _) _)
  rw [hq]
  push_cast
  rw [neg_eq_neg_one_mul, mul_zpow, ← _root_.inv_zpow', inv_neg_one]

theorem PositivityTheory.Rg.Bc.ArchbcB.B.m1 : PositivityTheory.Rg.Bc.ArchbcB.B.M1 :=
  PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first
