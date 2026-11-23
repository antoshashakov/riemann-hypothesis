module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def sglL (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AFplus L where
  toFun := GlobalTheory.InertUmax.sgl L v
  map_add' a b := (GlobalTheory.SplitLift.sgl_add v a b).symm
  map_smul' c r := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    exact (GlobalTheory.SplitLift.alg_mul_sgl v c r).symm

def lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AL L :=
  TensorProduct.map LinearMap.id (sglL v)

theorem lift_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : L)
    (r : v.adicCompletion (maximalRealSubfield L)) :
    lift v (a ⊗ₜ r) = a ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v r := rfl

theorem lift_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v (x * y) = lift v x * lift v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, lift_tmul, lift_tmul, lift_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.SplitLift.sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

theorem compAt_lift_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L v (lift v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx']

theorem compAt_lift_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L u (lift v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v r hu, tmul_zero]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

theorem conj_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    conjAL L (lift v x) =
      lift v (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    rw [lift_tmul, GlobalTheory.SplitLift.conjAL_tmul]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, lift_tmul]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]

def idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := lift v 1

theorem lift_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v x * idem v = lift v x := by
  rw [idem, ← lift_mul, mul_one]

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem idem_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idem v * idem v = (idem v : AL L) :=
  lift_mul_idem v 1

def glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L →+* AL L where
  toFun q := lift v q.1 + (1 - idem v) * q.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, mul_one]; rw [← idem]; ring
  map_mul' q q' := by
    simp only [Prod.fst_mul, Prod.snd_mul, lift_mul]
    have h1 := lift_mul_idem v q.1
    have h2 := lift_mul_idem v q'.1
    have h3 := idem_mul_idem v
    linear_combination q'.2 * h1 + q.2 * h2 - (q.2 * q'.2) * h3
  map_zero' := by simp
  map_add' q q' := by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring

theorem glue_apply (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    glue v q = lift v q.1 + (1 - idem v) * q.2 := rfl

theorem compAt_glue_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L v (glue v q) = q.1 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_same, compAt_lift_same]; ring

theorem compAt_glue_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L u (glue v q) = ReciprocityTheory.Aut.compAt L u q.2 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_ne v hu, compAt_lift_ne v hu]; ring

theorem conj_glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    conjAL L (glue v q) = glue v
      (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) q.1,
        conjAL L q.2) := by
  rw [glue_apply, glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, conj_lift, conj_lift, map_one]

theorem matrix_pair_ext {n : ℕ} {R₁ R₂ : Type*} (A B : Matrix (Fin n) (Fin n) (R₁ × R₂))
    (h₁ : A.map Prod.fst = B.map Prod.fst) (h₂ : A.map Prod.snd = B.map Prod.snd) : A = B :=
  Matrix.ext fun i j => Prod.ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

end GlobalTheory.InertLift
