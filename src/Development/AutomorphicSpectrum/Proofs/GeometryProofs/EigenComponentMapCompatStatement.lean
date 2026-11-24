module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenComponentMapCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.eigen_component_map_compat : ∀ (k k' V V' O : Type) [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V'), (∀ (c : k) x, j (c • x) = κ c • j x) → ∀ (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V'), (∀ a x, ρ' a (j x) = j (ρ a x)) → ∀ (σ : O →+* k) (x : V), eigComp ρ σ x ≠ 0 → eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map <;> assumption)
