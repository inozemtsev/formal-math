module

public import Green64.Library.Weights.Part027
public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part053
public import Green64.Library.Correlation.PrimeReturnHilbertSchur

@[expose] public section

/-!
# Correlation / PhysicalNoRepeatDensity

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalNoRepeatDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem fock_fibre_card {U : Type} [Fintype U] [DecidableEq U]
    {B : ℕ} (s : FockState U B) (hn : (fockMultiset s).Nodup) :
    Fintype.card {t : FockState U B // fockMultiset t=fockMultiset s} =
      Nat.factorial s.1.val := by
  let f : Equiv.Perm (Fin s.1.val) →
      {t : FockState U B // fockMultiset t=fockMultiset s} := fun e =>
    ⟨⟨s.1,fun i => s.2 (e i)⟩,
      Multiset.coe_eq_coe.mpr (e.ofFn_comp_perm s.2)⟩
  have hinj : Function.Injective s.2 := List.nodup_ofFn.mp hn
  have hi : Function.Injective f := by
    intro e d h
    have hv : (⟨s.1,fun i => s.2 (e i)⟩ : FockState U B) =
        ⟨s.1,fun i => s.2 (d i)⟩ := congrArg Subtype.val h
    have he : (fun i => s.2 (e i)) = (fun i => s.2 (d i)) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hv).2
    apply Equiv.ext
    intro i
    exact hinj (congrFun he i)
  have hs : Function.Surjective f := by
    intro t
    obtain ⟨e,he⟩ := source_original_FOCK_nodup_reindex434
      s t.val t.property.symm (t.property.symm ▸ hn)
    exact ⟨e,Subtype.ext he⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  simpa only [Fintype.card_perm,Fintype.card_fin] using hc.symm

/-- The original 1/j! Fock measure, summed over all ordered representatives,
equals the product atom mass on a no-repeat orbit. The factorial is derived
from the complete fibre, not dropped or assumed to cancel. -/
theorem source_original_FOCK_nodup_orbit_mass434
    {U : Type} [Fintype U] [DecidableEq U] {B : ℕ}
    (mu : U → ℝ) (m : Multiset U)
    (hm : m ∈ orbitSupport (U:=U) (B:=B)) (hn : m.Nodup) :
    orbitMass (B:=B) mu m = (m.map mu).prod := by
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hm
  rw [orbitMass,Finset.sum_subtype (p:=fun t : FockState U B =>
    fockMultiset t=fockMultiset s) _ (by intro t; simp)]
  have he (t : {t : FockState U B // fockMultiset t=fockMultiset s}) :
      fockMass mu t.val = fockMass mu s :=
    fockMass_multiset_eq mu t.val s t.property
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,fock_fibre_card s hn]
  have hj : (Nat.factorial s.1.val : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s.1.val
  simp only [nsmul_eq_mul,fockMass,fockMultiset,Multiset.map_coe,
    Multiset.prod_coe,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  field_simp

private theorem multiset_scaled_prod {U : Type} (m : Multiset U)
    (f : U → ℝ) (V : ℝ) :
    (m.map f).prod * V^m.card = (m.map (fun u => V*f u)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons u m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,pow_succ]
      rw [←ih]
      ring

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Exact original BIG orbit/sector mass. Pending atoms have mass V*mu;
the active array keeps its original activeMass. -/
theorem source_original_BIG_nodup_density434
    (M B : ℕ) (mu : P → ℝ) (V : ℝ)
    (a : Fin M → P) (m : Multiset (Atom P modulus))
    (hm : m ∈ orbitSupport (U:=Atom P modulus) (B:=B)) (hn : m.Nodup) :
    sourceOriginalMemoryBigDensityOrbitMass434 modulus M B mu V (a,m) =
      activeMass M mu a * (m.map (fun z => V*mu z.1)).prod := by
  unfold sourceOriginalMemoryBigDensityOrbitMass434
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hinner (s : FockState (Atom P modulus) B) :
      (∑ a' : Fin M → P,
        if sourceOriginalMemoryBigProjection434 modulus M B (a',s)=(a,m)
        then sourceOriginalMemoryBigDensityMass434 modulus M B mu V (a',s)
        else 0) =
      if fockMultiset s=m then activeMass M mu a *
        fockMass (sourceAtomMu mu) s * V^s.1.val else 0 := by
    by_cases h : fockMultiset s=m
    · simp [sourceOriginalMemoryBigProjection434,sourceOriginalMemoryBigDensityMass434,
        bigStateMass,h]
    · simp [sourceOriginalMemoryBigProjection434,h]
  simp_rw [hinner]
  have he :
      (∑ s : FockState (Atom P modulus) B,
        if fockMultiset s=m then activeMass M mu a *
          fockMass (sourceAtomMu mu) s * V^s.1.val else 0) =
      activeMass M mu a * (orbitMass (B:=B) (sourceAtomMu mu) m * V^m.card) := by
    simp only [orbitMass,Finset.sum_filter,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : fockMultiset s=m
    · have hj : s.1.val=m.card := by
        simpa only [fockMultiset,Multiset.coe_card,List.length_ofFn] using
          congrArg Multiset.card h
      simp only [h,ite_true,hj,mul_assoc]
    · simp [h]
  rw [he,source_original_FOCK_nodup_orbit_mass434 _ m hm hn,
    multiset_scaled_prod]
  rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The exact existing physical measure on a supported no-repeat orbit.
This is an equality with the original orbit sum and OLD sector density. -/
theorem source_original_FULL_nodup_density434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hs : ∀ g,(y.2 g).2 ∈ orbitSupport (U:=Atom (BP g) (bm g)) (B:=cap g))
    (hn : ∀ g,((y.2 g).2).Nodup) :
    physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y =
      groupStateMass SP sm (J+ell) Vs *
        ∏ g : BG,activeMass (J+ell) (mu g) (y.2 g).1 *
          ((y.2 g).2.map (fun z => Vb g*mu g z.1)).prod := by
  rw [source_original_memory_FULL_density_orbit_product434]
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_BIG_nodup_density434 (bm g) (J+ell) (cap g)
    (mu g) (Vb g) (y.2 g).1 (y.2 g).2 (hs g) (hn g)

/-- All no-repeat/support obligations follow from membership of the original
reachable Fock×seen carrier. No new hypothesis on the actual state, future
observable, or density is used. -/
theorem source_original_ACTUAL_true_density_pending_product434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu a =
      groupStateMass SP sm (J+ell) Vs *
        ∏ g : BG,activeMass (J+ell) (mu g) (a.val.1.2 g).1 *
          ((a.val.1.2 g).2.map (fun z => Vb g*mu g z.1)).prod := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  obtain ⟨x,hx,hproj⟩ := Finset.mem_image.mp ha.1
  have hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    rw [hproj]
    exact ha.2.2
  have hn := (source_original_PHYSICAL_reachable_pending434
    SP sm BP bm (J+ell) cap x a.val.2 hr).1
  apply source_original_FULL_nodup_density434 SP sm BP bm J ell cap
  · intro g
    refine Finset.mem_image.mpr ⟨(x.2 g).2,Finset.mem_univ _,?_⟩
    exact congrArg (fun y : FullPhysicalOutput SP sm BP bm (J+ell) => (y.2 g).2) hproj
  · intro g
    have he : fockMultiset (x.2 g).2=(a.val.1.2 g).2 :=
      congrArg (fun y : FullPhysicalOutput SP sm BP bm (J+ell) => (y.2 g).2) hproj
    rw [←he]
    exact (hn g).of_map (fun z => z.1)

end Green64Analytic.CorrelationSquare

end

end

