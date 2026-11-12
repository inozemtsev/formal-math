module

public import Green64.Library.Weights.MarkedPacketHilbert
public import Green64.Library.Correlation.Part042

@[expose] public section

/-!
# Weights / BigMarkedPacketHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalBigMarkedPacketHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (r : G → ℕ)

/-- The genuine simultaneous BIG fresh packet; its single history is the
set of all group-labelled primes, not independently resampled histories. -/
def sourceOriginalBigRefreshPacket434
    (x : (g : G) → Fin (r g) → BP g) : Finset (Sigma BP) :=
  Finset.univ.sigma (fun g => Finset.univ.image (x g))

def sourceOriginalBigRefreshMass434 (mu : (g : G) → BP g → ℝ)
    (x : (g : G) → Fin (r g) → BP g) : ℝ :=
  ∏ g,∏ j,mu g (x g j)

private theorem big_packet_mem
    (x : (g : G) → Fin (r g) → BP g) (g : G) (p : BP g) :
    (⟨g,p⟩ : Sigma BP) ∈ sourceOriginalBigRefreshPacket434 BP r x ↔
      ∃ j,x g j=p := by
  simp [sourceOriginalBigRefreshPacket434]

private theorem big_packet_subset
    (x : (g : G) → Fin (r g) → BP g) (S : Finset (Sigma BP)) :
    sourceOriginalBigRefreshPacket434 BP r x ⊆ S ↔
      ∀ g j,(⟨g,x g j⟩ : Sigma BP) ∈ S := by
  constructor
  · intro h g j
    exact h ((big_packet_mem BP r x g (x g j)).2 ⟨j,rfl⟩)
  · intro h p hp
    obtain ⟨g,p⟩ := p
    obtain ⟨j,rfl⟩ := (big_packet_mem BP r x g p).1 hp
    exact h g j

private theorem big_packet_fresh
    (x : (g : G) → Fin (r g) → BP g) (S : Finset (Sigma BP)) :
    Disjoint S (sourceOriginalBigRefreshPacket434 BP r x) ↔
      sourceOriginalBigRefreshPacket434 BP r x ⊆ Sᶜ := by
  constructor
  · intro hd p hp
    exact Finset.mem_compl.mpr (fun hs => Finset.disjoint_left.mp hd hs hp)
  · intro h
    exact Finset.disjoint_left.mpr (fun p hp hb => (Finset.mem_compl.mp (h hb)) hp)

/-- Exact restriction of the original full BIG product mass to one seen
set. All groups are conditioned on that SAME set. -/
theorem source_original_BIG_PACKET_seen_mass434
    (mu : (g : G) → BP g → ℝ) (S : Finset (Sigma BP)) :
    (∑ x : ((g : G) → Fin (r g) → BP g),
      if sourceOriginalBigRefreshPacket434 BP r x ⊆ S then
        sourceOriginalBigRefreshMass434 BP r mu x else 0) =
    ∏ g : G,(∑ p : BP g,if (⟨g,p⟩ : Sigma BP) ∈ S then mu g p else 0)^(r g) := by
  classical
  simp_rw [big_packet_subset]
  have hx (x : (g : G) → Fin (r g) → BP g) :
      (if ∀ g j,(⟨g,x g j⟩ : Sigma BP) ∈ S then
        sourceOriginalBigRefreshMass434 BP r mu x else 0) =
      ∏ g : G,∏ j : Fin (r g),
        if (⟨g,x g j⟩ : Sigma BP) ∈ S then mu g (x g j) else 0 := by
    symm
    simp only [Finset.prod_ite_zero,Finset.mem_univ,forall_true_left,
      sourceOriginalBigRefreshMass434]
  simp_rw [hx]
  rw [←Fintype.prod_sum (fun (g : G) (v : Fin (r g) → BP g) =>
    ∏ j : Fin (r g),if (⟨g,v j⟩ : Sigma BP) ∈ S then mu g (v j) else 0)]
  apply Finset.prod_congr rfl
  intro g hg
  rw [←Fintype.prod_sum (fun (_ : Fin (r g)) (p : BP g) =>
    if (⟨g,p⟩ : Sigma BP) ∈ S then mu g p else 0)]
  simp

/-- Actual simultaneous product-law fresh replacement on BIG x seen.
No independence of K or of the complex future is required. Tilted masses
are retained exactly in the displayed gain. -/
theorem source_original_BIG_MARKED_PACKET_Hilbert434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (K : ((g : G) → Fin (r g) → BP g) → Finset (Sigma BP) →
      ((g : G) → Fin (r g) → BP g) → ℂ)
    (hK : ∀ x S y,‖K x S y‖ ≤ 1)
    (f : ((g : G) → Fin (r g) → BP g) → Finset (Sigma BP) → ℂ) :
    sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu)
      (sourceOriginalMarkedPacket434 (sourceOriginalBigRefreshMass434 BP r mu)
        (sourceOriginalBigRefreshPacket434 BP r) K f) ≤
    (∏ g : G,((∑ p : BP g,mu g p)^2/4)^(r g)) *
      sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu) f := by
  classical
  apply source_original_MARKED_PACKET_Hilbert434
  · intro x
    apply Finset.prod_nonneg
    intro g hg
    exact Finset.prod_nonneg (fun j _ => hmu g (x g j))
  · exact Finset.prod_nonneg (fun g _ => by positivity)
  · intro S
    simp_rw [big_packet_fresh,source_original_BIG_PACKET_seen_mass434]
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro g hg
      apply mul_nonneg <;> apply pow_nonneg
      · exact Finset.sum_nonneg (fun p _ => by split_ifs; exact hmu g p; exact le_rfl)
      · exact Finset.sum_nonneg (fun p _ => by split_ifs; exact hmu g p; exact le_rfl)
    · intro g hg
      let a : ℝ := ∑ p : BP g,if (⟨g,p⟩ : Sigma BP) ∈ S then mu g p else 0
      let b : ℝ := ∑ p : BP g,if (⟨g,p⟩ : Sigma BP) ∈ Sᶜ then mu g p else 0
      have ha : 0 ≤ a :=
        Finset.sum_nonneg (fun p _ => by split_ifs; exact hmu g p; exact le_rfl)
      have hb : 0 ≤ b :=
        Finset.sum_nonneg (fun p _ => by split_ifs; exact hmu g p; exact le_rfl)
      have hab : a+b=∑ p : BP g,mu g p := by
        dsimp only [a,b]
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : (⟨g,p⟩ : Sigma BP) ∈ S <;> simp [h]
      change a^(r g)*b^(r g) ≤ _
      rw [←mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg ha hb)
      nlinarith [sq_nonneg (a-b)]
  · exact hK

/-- Normalized true prime laws give one factor 1/4 per refreshed mark
through the WHOLE simultaneous BIG packet, including arbitrary joint tests. -/
theorem source_original_BIG_MARKED_PACKET_normalized_Hilbert434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (K : ((g : G) → Fin (r g) → BP g) → Finset (Sigma BP) →
      ((g : G) → Fin (r g) → BP g) → ℂ)
    (hK : ∀ x S y,‖K x S y‖ ≤ 1)
    (f : ((g : G) → Fin (r g) → BP g) → Finset (Sigma BP) → ℂ) :
    sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu)
      (sourceOriginalMarkedPacket434 (sourceOriginalBigRefreshMass434 BP r mu)
        (sourceOriginalBigRefreshPacket434 BP r) K f) ≤
    (1/4:ℝ)^(∑ g,r g) *
      sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu) f := by
  have h := source_original_BIG_MARKED_PACKET_Hilbert434 BP r mu hmu K hK f
  simpa only [hmass,one_pow,Finset.prod_pow_eq_pow_sum] using h

end Green64Analytic.CorrelationSquare

end

end

