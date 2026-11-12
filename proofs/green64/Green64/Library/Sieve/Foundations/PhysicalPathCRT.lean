module

public import Green64.Library.Weights.ActiveResidueTransfer
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Sieve / Foundations / PhysicalPathCRT

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPhysicalPathCRT -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact local weight of an actually marked physical path: an active
prime forces divisibility; every other visit keeps its original damping.
In particular active primes are still damped at their unmarked visits. -/
def b641PathPrimeWeight434 (visits : Finset ℕ) (activeAt : ℕ → Finset ℕ)
    (eta : ℕ → ℝ) (offset : ℕ → ℤ) (p r : ℕ) : ℝ :=
  ∏ i ∈ visits,
    if p ∈ activeAt i then
      (if (r:ZMod p)+(offset i:ZMod p)=0 then 1 else 0)
    else (if (r:ZMod p)+(offset i:ZMod p)=0 then eta i else 1)

private theorem b641_local_nonneg (visits : Finset ℕ) (activeAt : ℕ → Finset ℕ)
    (eta : ℕ → ℝ) (offset : ℕ → ℤ) (heta : ∀ i ∈ visits,0≤eta i)
    (p r : ℕ) : 0≤b641PathPrimeWeight434 visits activeAt eta offset p r := by
  apply Finset.prod_nonneg
  intro i hi
  split
  · split <;> norm_num
  · split
    · exact heta i hi
    · norm_num

private theorem b641_local_physical (visits : Finset ℕ) (activeAt : ℕ → Finset ℕ)
    (eta : ℕ → ℝ) (offset : ℕ → ℤ) (p n : ℕ) :
    b641PathPrimeWeight434 visits activeAt eta offset p (n%p) =
      ∏ i ∈ visits, if p ∈ activeAt i then
        (if (p:ℤ) ∣ (n:ℤ)+offset i then 1 else 0)
      else (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1) := by
  apply Finset.prod_congr rfl
  intro i hi
  have he : ((n%p:ℕ):ZMod p)+(offset i:ZMod p)=0 ↔ (p:ℤ) ∣ (n:ℤ)+offset i := by
    simpa only [ZMod.natCast_mod,Int.cast_add,Int.cast_natCast] using
      ZMod.intCast_zmod_eq_zero_iff_dvd ((n:ℤ)+offset i) p
  simp only [he]

private theorem b641_local_inactive (visits : Finset ℕ) (activeAt : ℕ → Finset ℕ)
    (eta : ℕ → ℝ) (offset : ℕ → ℤ) (p : ℕ)
    (hp : p ∉ visits.biUnion activeAt) (r : ℕ) :
    b641PathPrimeWeight434 visits activeAt eta offset p r =
      1-b637PathResidueLoss434 visits eta offset p r := by
  unfold b637PathResidueLoss434
  rw [sub_sub_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  have hn : p ∉ activeAt i := fun hh => hp (Finset.mem_biUnion.mpr ⟨i,hi,hh⟩)
  simp only [hn,ite_false]

private theorem b641_prod_split (G active : Finset ℕ) (ha : active ⊆ G) (w : ℕ → ℝ) :
    (∏ p ∈ G,w p) = (∏ p ∈ active,w p)*(∏ p ∈ G\active,w p) := by
  have hd : Disjoint active (G\active) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  have hh := Finset.prod_union (f := w) hd
  rw [Finset.union_sdiff_of_subset ha] at hh
  exact hh

/-- Genuine full physical-path CRT transference on the original Parity P
family. Both active indicators and inactive damping are literal p|n+h_i
conditions in the SAME integer. The model is the product of the full
local residue means, including every active prime's unmarked visits.
The source retention is q_i=sqrt(1/2) at 0,N and q_i=1/2 inside, exactly
sourceVisitQ (and not the complementary sourceVisitEta). All compatible,
incompatible and zero-model paths are covered by the same inequality. -/
theorem b641_eventually_actual_parity_physical_path_CRT434
    (E gamma : ℝ) (hE : 0≤E) (hgamma : 0<gamma) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    let visits := Finset.range (N+1)
    ∀ activeAt : ℕ → Finset ℕ,
      (∀ i ∈ visits,activeAt i ⊆ sourceNativeOriginalG434 20 L) →
      (∀ i ∈ visits,(activeAt i).card ≤ J*(sourceOriginalPAllGroupIndices 20 L).card) →
    ∀ lo hi : ℕ, Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
    ∀ offset : ℕ → ℤ,
    let eta := sourceVisitQ (1/2:ℝ) N
    let w := b641PathPrimeWeight434 visits activeAt eta offset
    let model := ∏ p ∈ sourceNativeOriginalG434 20 L,
      (∑ r ∈ Finset.range p,w p r)/(p:ℝ)
    |(∑ n ∈ Finset.Ico lo hi,
      ∏ p ∈ sourceNativeOriginalG434 20 L, ∏ i ∈ visits,
        if p ∈ activeAt i then
          (if (p:ℤ) ∣ (n:ℤ)+offset i then 1 else 0)
        else (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1)) -
        ((hi-lo:ℕ):ℝ)*model| ≤
      (((hi-lo:ℕ):ℝ)*model)*L^(-E*(N:ℝ)) := by
  filter_upwards [b641_eventually_actual_parity_active_weight_CRT434 E gamma hE hgamma J,
    eventually_ge_atTop (1:ℝ)] with L h hL
  dsimp only at h ⊢
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let visits := Finset.range (N+1)
  intro activeAt hsub hcard lo hi hH offset
  let active := visits.biUnion activeAt
  let G := sourceNativeOriginalG434 20 L
  let P := G\active
  let eta := sourceVisitQ (1/2:ℝ) N
  let w := b641PathPrimeWeight434 visits activeAt eta offset
  let loss := b637PathResidueLoss434 visits eta offset
  have ha : active ⊆ G := by
    intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi hp
  have hc : active.card ≤ J*(N+1)*(sourceOriginalPAllGroupIndices 20 L).card := by
    calc
      _ ≤ ∑ i ∈ visits,(activeAt i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ visits,J*(sourceOriginalPAllGroupIndices 20 L).card :=
        Finset.sum_le_sum (fun i hi => hcard i hi)
      _ = _ := by simp only [visits,Finset.sum_const,Finset.card_range,nsmul_eq_mul]; norm_cast; ring
  have heta : ∀ i ∈ visits,0≤eta i ∧ eta i≤1 := by
    intro i hi
    dsimp [eta,sourceVisitQ]
    split
    · have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
      have hn := Real.sqrt_nonneg (1/2:ℝ)
      exact ⟨hn,by nlinarith⟩
    · norm_num
  have hw : ∀ p ∈ active,∀ r,0≤w p r := fun p hp r =>
    b641_local_nonneg visits activeAt eta offset (fun i hi => (heta i hi).1) p r
  have htrans := h active ha hc w hw lo hi hH eta offset heta
  have hInactive (p : ℕ) (hp : p ∈ P) (r : ℕ) : w p r = 1-loss p r :=
    b641_local_inactive visits activeAt eta offset p (Finset.mem_sdiff.mp hp).2 r
  have hMean (p : ℕ) (hp : p ∈ P) :
      (∑ r ∈ Finset.range p,w p r)/(p:ℝ) = 1-b637ResidueMean434 loss p := by
    have hp0 : (p:ℝ)≠0 := by
      exact_mod_cast (b638_actual_full_P_range434 L hL p (Finset.mem_sdiff.mp hp).1).1.ne_zero
    simp_rw [hInactive p hp]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,b637ResidueMean434,b637ResidueTotal434]
    rw [sub_div,div_self hp0]
  have hModel : (∏ p ∈ G,(∑ r ∈ Finset.range p,w p r)/(p:ℝ)) =
      (∏ p ∈ active,(∑ r ∈ Finset.range p,w p r)/(p:ℝ))*
      (∏ p ∈ P,(1-b637ResidueMean434 loss p)) := by
    rw [b641_prod_split G active ha]
    congr 1
    exact Finset.prod_congr rfl hMean
  have hPhys (n : ℕ) :
      (∏ p ∈ G,∏ i ∈ visits,if p ∈ activeAt i then
          (if (p:ℤ) ∣ (n:ℤ)+offset i then (1:ℝ) else 0)
        else (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1)) =
      (∏ p ∈ active,w p (n%p)) *
      (∏ p ∈ P,∏ i ∈ visits,if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1) := by
    calc
      _ = ∏ p ∈ G,w p (n%p) := by
        exact Finset.prod_congr rfl (fun p hp => (b641_local_physical visits activeAt eta offset p n).symm)
      _ = _ := by
        rw [b641_prod_split G active ha]
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        rw [hInactive p hp]
        exact b637_physical_path_loss_factor434 visits eta offset p n
  change |(∑ n ∈ Finset.Ico lo hi,∏ p ∈ G,∏ i ∈ visits,
      if p ∈ activeAt i then (if (p:ℤ) ∣ (n:ℤ)+offset i then (1:ℝ) else 0)
      else (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1)) -
        ((hi-lo:ℕ):ℝ)*(∏ p ∈ G,(∑ r ∈ Finset.range p,w p r)/(p:ℝ))| ≤
      (((hi-lo:ℕ):ℝ)*(∏ p ∈ G,(∑ r ∈ Finset.range p,w p r)/(p:ℝ)))*L^(-E*(N:ℝ))
  simp_rw [hPhys]
  rw [hModel]
  simpa only [mul_assoc] using htrans
end Green64Analytic.SourceBlockSieve

end

end

