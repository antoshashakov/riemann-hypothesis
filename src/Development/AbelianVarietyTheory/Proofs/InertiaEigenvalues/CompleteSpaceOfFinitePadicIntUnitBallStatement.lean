module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceOfFinitePadicIntUnitBall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  first | exact @GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | exact GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | (intros; apply GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall <;> assumption)
