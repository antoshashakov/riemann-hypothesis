module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.function_field_ratio_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | exact GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin <;> assumption)
