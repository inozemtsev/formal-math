module

public import Green64.Library.Weights.ReachableBackgroundEncoding

@[expose] public section

/-!
# Weights / ReachableBackgroundRow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalReachableBackgroundRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

/-- The actual full physical inventory controls every pending numerical
inventory. It is not a new hypothesis about a reduced state space. -/
theorem source_original_REACHABLE_pending_inventory434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG) :
    (((y.2 g).2).map (fun z => bm g z.1)).Nodup ∧
      ∀ z ∈ (y.2 g).2,bm g z.1 ∈ seen := by
  have hle : (((y.2 g).2).map (fun z => bm g z.1)) ≤
      sourceOriginalPhysicalInventory434 SP sm BP bm M y := by
    apply le_trans (show _ ≤ sourceOriginalBigInventory434 (bm g) M (y.2 g).1 (y.2 g).2 from
      le_add_of_nonneg_left (zero_le))
    exact Finset.single_le_sum (fun i hi => (zero_le : (0:Multiset ℕ) ≤
      sourceOriginalBigInventory434 (bm i) M (y.2 i).1 (y.2 i).2)) (Finset.mem_univ g)
  refine ⟨Multiset.nodup_of_le hle hy.1,?_⟩
  intro z hz
  exact hy.2 _ (Multiset.mem_of_le hle (Multiset.mem_map.mpr ⟨z,hz,rfl⟩))

/-- Exact embedding of the genuine B-filtered pending component of any
reachable original Fock output, preserving the entire numerical seen
set and explicitly removing padded coordinates from the observable. -/
theorem source_original_REACHABLE_background_encoding434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (g : BG) (B : Finset (BP g)) (shift : ℤ) :
    ∃ s : SourceOriginalPrimeReturnProductState434 (bm g),
      (∀ p,p ∉ B → s p=.retired) ∧
      sourceOriginalPrimeProductPending434 (bm g) shift s =
        ((y.2 g).2).filter (fun z => z.1 ∈ B) ∧
      (seen \ B.image (bm g)) ∪
        (sourceOriginalPrimeProductSeen434 (bm g) s ∩ B).image (bm g) = seen := by
  have h := source_original_REACHABLE_pending_inventory434 SP sm BP bm M y seen hy g
  exact source_original_NUMERIC_PENDING_background_encoding434 (bm g) shift B
    (y.2 g).2 seen h.1 h.2

/-- Actual background component of a reachable original state admits the
certified signed return-matrix formula. The continuation remains an
arbitrary joint function, so all other original data may be retained. -/
theorem source_original_REACHABLE_background_G_return_matrix434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (g : BG) (B : Finset (BP g)) (hi : Function.Injective (bm g))
    (shift : ℤ) (eta V : ℝ) (mu : BP g → ℝ)
    (F : Multiset (Atom (BP g) (bm g)) → Finset ℕ → ℂ) :
    ∃ s : SourceOriginalPrimeReturnProductState434 (bm g),
      (∀ p,p ∉ B → s p=.retired) ∧
      sourceOriginalPrimeProductPending434 (bm g) shift s =
        ((y.2 g).2).filter (fun z => z.1 ∈ B) ∧
      sourceOriginalPhysicalNumericRestrictedPoolG434 (bm g) B eta V mu
        (((y.2 g).2).filter (fun z => z.1 ∈ B)) seen F =
      sourceOriginalPrimeProductReturnRow434 (bm g) shift s eta V mu
        (fun t => F (sourceOriginalPrimeProductPending434 (bm g) shift t)
          ((seen \ B.image (bm g)) ∪
            (sourceOriginalPrimeProductSeen434 (bm g) t ∩ B).image (bm g))) := by
  obtain ⟨s,hs,hpend,hseen⟩ := source_original_REACHABLE_background_encoding434
    SP sm BP bm M y seen hy g B shift
  refine ⟨s,hs,hpend,?_⟩
  have hext : ∀ p ∈ B,bm g p ∉ seen \ B.image (bm g) := by
    intro p hp h
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_image_of_mem (bm g) hp)
  have h := source_original_NUMERIC_BACKGROUND_POOL_G_return_matrix434
    (bm g) B shift s hs hi (seen \ B.image (bm g)) hext eta V mu F
  rwa [hpend,hseen] at h
end Green64Analytic.CorrelationSquare

end

end

