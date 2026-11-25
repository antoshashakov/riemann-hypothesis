module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexPolyGradingFiniteExact
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
theorem _root_.GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), (∀ p, Module.Finite R ((cubeComplex (grCube ι (polyGrading ι R) n)).homology p)) ∧ (1 ≤ n → ∀ p, (cubeComplex (grCube ι (polyGrading ι R) n)).ExactAt p) := by
  first | exact @GlobalTheory.cubeComplex_polyGrading_finite_exact | exact GlobalTheory.cubeComplex_polyGrading_finite_exact | (intros; apply GlobalTheory.cubeComplex_polyGrading_finite_exact <;> assumption)
