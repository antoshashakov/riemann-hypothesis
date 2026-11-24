module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Degrees O K l e a := by
  first | exact @GlobalTheory.DegreeRaise.main | exact GlobalTheory.DegreeRaise.main | (intros; apply GlobalTheory.DegreeRaise.main <;> assumption)
