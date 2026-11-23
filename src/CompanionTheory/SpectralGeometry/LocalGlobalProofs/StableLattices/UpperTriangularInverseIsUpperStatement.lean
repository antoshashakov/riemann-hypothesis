module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.upper_triangular_inverse_is_upper : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | exact GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | (intros; apply GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv <;> assumption)
