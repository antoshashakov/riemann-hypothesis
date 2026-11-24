module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotient
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_kernel_prime_quotient : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (b : Sp k ⟶ S) (M : LieModel (splitTorus S X) b (X →+ k)), IsCocharLie M → ∀ δ : X →+ k, δ ≠ 0 → M.pt δ ≫ u = 1 → ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ KillsOver u ψ.ker b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed | exact GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed | (intros; apply GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed <;> assumption)
