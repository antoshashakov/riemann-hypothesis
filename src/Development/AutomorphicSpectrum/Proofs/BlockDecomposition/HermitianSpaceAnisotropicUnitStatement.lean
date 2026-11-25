module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSpaceAnisotropicUnit
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.hermitian_space_anisotropic_unit : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nontrivial V → ∃ w : V, IsUnit (B.h w w) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | exact GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm <;> assumption)
