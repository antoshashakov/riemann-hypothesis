module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorIdealMapInjective
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_ideal_map_injective : ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | exact GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map | (intros; apply GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map <;> assumption)
