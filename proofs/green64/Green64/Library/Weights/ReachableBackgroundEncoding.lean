module

public import Green64.Library.Weights.Part061
public import Green64.Library.Correlation.Part028

@[expose] public section

/-!
# Weights / ReachableBackgroundEncoding

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalReachableBackgroundEncoding -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

private theorem pending_fibres (pending : Multiset (Atom P modulus)) :
    (∑ p,pending.filter (fun z => z.1=p)) = pending := by
  induction pending using Multiset.induction with
  | empty => simp
  | cons z pending ih =>
      simp only [Multiset.filter_cons,Finset.sum_add_distrib,ih]
      simp

/-- Every true once-per-label pending/seen state has an exact return-state
encoding. Existence is proved from the physical inventory condition. -/
theorem source_original_PHYSICAL_PENDING_return_encoding434
    (shift : ℤ) (pending : Multiset (Atom P modulus)) (seen : Finset P)
    (hn : (pending.map (fun z => z.1)).Nodup)
    (hs : ∀ z ∈ pending,z.1 ∈ seen) :
    ∃ s : SourceOriginalPrimeReturnProductState434 modulus,
      sourceOriginalPrimeProductPending434 modulus shift s=pending ∧
      sourceOriginalPrimeProductSeen434 modulus s=seen := by
  have hp (p : P) : ∃ t : SourceOriginalGhostReturnState434 (ZMod (modulus p)),
      sourceOriginalOnePrimePending434 modulus p shift t =
        pending.filter (fun z => z.1=p) ∧
      sourceOriginalOnePrimeSeen434 t = decide (p ∈ seen) := by
    by_cases h : ∃ r : ZMod (modulus p),(⟨p,r⟩ : Atom P modulus) ∈ pending
    · obtain ⟨r,hr⟩ := h
      refine ⟨.pending (r-(shift : ZMod (modulus p))),?_,?_⟩
      · have hf : pending.filter (fun z => z.1=p) =
            ({⟨p,r⟩} : Multiset (Atom P modulus)) := by
          apply (Multiset.Nodup.ext (Multiset.Nodup.filter _ (Multiset.Nodup.of_map _ hn))
            (by simp)).mpr
          intro z
          simp only [Multiset.mem_filter,Multiset.mem_singleton]
          constructor
          · intro ⟨hz,hzp⟩
            exact Multiset.inj_on_of_nodup_map hn z hz ⟨p,r⟩ hr hzp
          · intro hz
            subst z
            exact ⟨hr,rfl⟩
        simp [sourceOriginalOnePrimePending434,hf]
      · have hps := hs ⟨p,r⟩ hr
        simp [sourceOriginalOnePrimeSeen434,hps]
    · have hf : pending.filter (fun z => z.1=p)=0 := by
        apply Multiset.filter_eq_nil.mpr
        rintro ⟨a,r⟩ hz he
        change a=p at he
        subst a
        exact h ⟨r,hz⟩
      by_cases hps : p ∈ seen
      · exact ⟨.retired,by simp [sourceOriginalOnePrimePending434,hf],
          by simp [sourceOriginalOnePrimeSeen434,hps]⟩
      · exact ⟨.unborn,by simp [sourceOriginalOnePrimePending434,hf],
          by simp [sourceOriginalOnePrimeSeen434,hps]⟩
  choose s hpend hseen using hp
  refine ⟨s,?_,?_⟩
  · unfold sourceOriginalPrimeProductPending434
    simp_rw [hpend]
    exact pending_fibres modulus pending
  · ext p
    rw [source_original_PRIME_PRODUCT_seen_mem434,hseen]
    simp

/-- Restricting an actual inventory to B yields an exact padded encoding.
The original numerical seen set is recovered without losing its outside
part; outside return coordinates are retired and are not observable. -/
theorem source_original_NUMERIC_PENDING_background_encoding434
    (shift : ℤ) (B : Finset P) (pending : Multiset (Atom P modulus))
    (seen : Finset ℕ)
    (hn : (pending.map (fun z => modulus z.1)).Nodup)
    (hs : ∀ z ∈ pending,modulus z.1 ∈ seen) :
    ∃ s : SourceOriginalPrimeReturnProductState434 modulus,
      (∀ p,p ∉ B → s p=.retired) ∧
      sourceOriginalPrimeProductPending434 modulus shift s =
        pending.filter (fun z => z.1 ∈ B) ∧
      (seen \ B.image modulus) ∪
        (sourceOriginalPrimeProductSeen434 modulus s ∩ B).image modulus = seen := by
  let S := pending.filter (fun z => z.1 ∈ B)
  let A := B.filter (fun p => modulus p ∈ seen)
  let padded := A ∪ (Finset.univ \ B)
  have hlabel : (pending.map (fun z => z.1)).Nodup := by
    apply Multiset.Nodup.of_map modulus
    simpa only [Multiset.map_map,Function.comp_def] using hn
  have hSn : (S.map (fun z => z.1)).Nodup :=
    Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) hlabel
  have hSs : ∀ z ∈ S,z.1 ∈ padded := by
    intro z hz
    obtain ⟨hz,hB⟩ := Multiset.mem_filter.mp hz
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB,hs z hz⟩)
  obtain ⟨s,hpend,hseen⟩ := source_original_PHYSICAL_PENDING_return_encoding434
    modulus shift S padded hSn hSs
  have hout : ∀ p,p ∉ B → s p=.retired := by
    intro p hp
    have hzero : sourceOriginalOnePrimePending434 modulus p shift (s p)=0 := by
      rw [←source_original_PRIME_PRODUCT_pending_filter434,hpend]
      apply Multiset.filter_eq_nil.mpr
      intro z hz he
      exact hp (he ▸ (Multiset.mem_filter.mp hz).2)
    have hsp : sourceOriginalOnePrimeSeen434 (s p)=true := by
      apply (source_original_PRIME_PRODUCT_seen_mem434 modulus s p).mp
      rw [hseen]
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,hp⟩)
    cases h : s p with
    | unborn => simp [h,sourceOriginalOnePrimeSeen434] at hsp
    | retired => rfl
    | pending r =>
        have hh := congrArg Multiset.card hzero
        simp [h,sourceOriginalOnePrimePending434] at hh
  refine ⟨s,hout,hpend,?_⟩
  have hB : sourceOriginalPrimeProductSeen434 modulus s ∩ B = A := by
    rw [hseen]
    ext p
    simp only [padded,A,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff,
      Finset.mem_univ,Finset.mem_filter]
    tauto
  rw [hB]
  have him : A.image modulus = seen ∩ B.image modulus := by
    ext n
    simp only [A,Finset.mem_image,Finset.mem_filter,Finset.mem_inter]
    constructor
    · rintro ⟨p,⟨hp,hps⟩,rfl⟩
      exact ⟨hps,p,hp,rfl⟩
    · rintro ⟨hns,p,hp,rfl⟩
      exact ⟨p,⟨hp,hns⟩,rfl⟩
  rw [him]
  ext n
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto
end Green64Analytic.CorrelationSquare

end

end

