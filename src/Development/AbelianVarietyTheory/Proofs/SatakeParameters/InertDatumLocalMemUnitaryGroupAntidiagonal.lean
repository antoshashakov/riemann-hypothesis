module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalForm

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_conj_by_inverse_pair_preserves_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ}
    (P Q M J : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hM2 : Formalism.UG.cT σ M * M = 1)
    (hJ : Formalism.UG.cT σ P * P = J) : Formalism.UG.cT σ (Q * M * P) * J * (Q * M * P) = J := by
  have hQP : Formalism.UG.cT σ Q * Formalism.UG.cT σ P = 1 := by rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  subst hJ
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT σ P * Formalism.UG.cT σ M * (Formalism.UG.cT σ Q * Formalism.UG.cT σ P) * (P * Q) * M * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * P := by
        rw [hQP, hPQ, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc (Formalism.UG.cT σ P), hM2, Matrix.mul_one]

open Formalism.UG in
theorem inertLoc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  first
  | exact @_root_.GlobalTheory.LocalUnitary.loc_mem_GU
  | exact _root_.GlobalTheory.LocalUnitary.loc_mem_GU
  | (apply _root_.GlobalTheory.LocalUnitary.loc_mem_GU <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalUnitary.loc_mem_GU <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalUnitary.loc_mem_GU <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalUnitary.loc_mem_GU ..)

end GlobalTheory
