module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.degenerationSeriesTerms_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  first | exact @GlobalTheory.Ex.Nest.txT_nest | exact GlobalTheory.Ex.Nest.txT_nest | (intros; apply GlobalTheory.Ex.Nest.txT_nest <;> assumption)
