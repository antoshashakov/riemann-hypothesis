module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneAddJacobsonTensor
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.isUnit_one_add_jacobson_tensor : ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing R] [Algebra O R] (x : O' ⊗[O] R), x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson → IsUnit (1 + x) := by
  first | exact @GlobalTheory.CompanionTheory.JacUnit.main | exact GlobalTheory.CompanionTheory.JacUnit.main | (intros; apply GlobalTheory.CompanionTheory.JacUnit.main <;> assumption)
