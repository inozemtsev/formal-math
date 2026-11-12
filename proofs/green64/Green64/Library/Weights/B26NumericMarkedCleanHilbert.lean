module

public import Green64.Library.Weights.B26MarkedCleanActiveHilbert
public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part047

@[expose] public section

/-!
# Weights / B26NumericMarkedCleanHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26NumericMarkedCleanHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ)
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
local notation "A" => SourceOriginalB26Active434 BP J ell

/-- The same marked CLEAN BIG row on the actual NUMERICAL history.
No separate per-group histories or history resampling is introduced. -/
def sourceOriginalB26NumericMarkedClean434
    (mu : (g : G) → BP g → ℝ)
    (K : A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → ℂ)
    (s : A) (S : Finset ℕ) : ℂ :=
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image (fun p : Sigma BP => bm p.1 p.2) ⊆ S then
    ∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu t).image (fun p : Sigma BP => bm p.1 p.2)) then
        K s S t*f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu t).image (fun p : Sigma BP => bm p.1 p.2))
       else 0)
  else 0

def sourceOriginalB26NumericActiveEnergy434
    (mu : (g : G) → BP g → ℝ) (f : A → Finset ℕ → ℂ) : ℝ :=
  ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    ∑ s : A,sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu s * ‖f s S‖^2

private theorem pool_as_image :
    sourceOriginalMemoryBirthPool434 BP bm = (Finset.univ : Finset (Sigma BP)).image (fun p : Sigma BP => bm p.1 p.2) := by
  ext n
  constructor
  · intro hn
    obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨⟨g,p⟩,Finset.mem_univ _,rfl⟩
  · intro hn
    obtain ⟨⟨g,p⟩,hp,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

/-- Counting the REAL numeric histories is exactly counting tagged histories
under the proved global prime injection. There is no multiplicity factor. -/
theorem source_original_B26_NUMERIC_HISTORY_energy434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2)) (mu : (g : G) → BP g → ℝ)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f =
    sourceOriginalB26MarkedActiveEnergy434 BP J ell mu
      (fun s S => f s (S.image (fun p : Sigma BP => bm p.1 p.2))) := by
  unfold sourceOriginalB26NumericActiveEnergy434
    sourceOriginalB26MarkedActiveEnergy434 sourceOriginalMarkedPacketEnergy434
  rw [pool_as_image,Finset.powerset_image,
    Finset.sum_image (Finset.image_injective hi).injOn]
  have hu : (Finset.univ : Finset (Sigma BP)).powerset =
      (Finset.univ : Finset (Finset (Sigma BP))) := by ext S; simp
  rw [hu]

/-- Literal numeric no-rebirth and history union commute with the actual
global prime injection. The original two endpoint labels are preserved. -/
theorem source_original_B26_NUMERIC_CLEAN_row434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2)) (mu : (g : G) → BP g → ℝ)
    (K : A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → ℂ)
    (s : A) (S : Finset (Sigma BP)) :
    sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K f s (S.image (fun p : Sigma BP => bm p.1 p.2)) =
    sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu
      (fun a seen b => K a (seen.image (fun p : Sigma BP => bm p.1 p.2)) b)
      (fun a seen => f a (seen.image (fun p : Sigma BP => bm p.1 p.2))) s S := by
  unfold sourceOriginalB26NumericMarkedClean434 sourceOriginalB26MarkedCleanActive434
  simp only [Finset.image_subset_image_iff hi,Finset.disjoint_image hi,Finset.image_union]

/-- Actual numerical-history CLEAN BIG energy bound in the unchanged
product density, with the full complex coefficient cap paid explicitly. -/
theorem source_original_B26_NUMERIC_CLEAN_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2)) (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p) (C : ℝ) (hC : 0 ≤ C)
    (K : A → Finset ℕ → A → ℂ) (hK : ∀ s S t,‖K s S t‖ ≤ C)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  rw [source_original_B26_NUMERIC_HISTORY_energy434 BP bm J ell hi,
    source_original_B26_NUMERIC_HISTORY_energy434 BP bm J ell hi]
  simp_rw [source_original_B26_NUMERIC_CLEAN_row434 BP bm J ell m hmJ nu hi]
  exact source_original_B26_MARKED_CLEAN_bounded_Hilbert434 BP J ell m hmJ nu
    mu hmu C hC _ (fun s S t => hK s (S.image (fun p : Sigma BP => bm p.1 p.2)) t) _

variable (P : G → Finset ℕ)
variable [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]

/-- The actual canonical comparison coefficient, including its joint
auxiliary ban, original oriented Mellin/Fourier phase and reverse-edge
RAW/comparison transposition. keep can impose the original remaining gates. -/
def sourceOriginalB26CanonicalNumericCleanK434
    (V : G → ℝ) (Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ) (dsmall : ℕ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (keep : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell →
      Finset ℕ → SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Prop)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (S : Finset ℕ)
    (t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) : ℂ :=
  if keep s S t ∧ sourceOriginalB26FrozenAuxBan434
      (fun g => {p : ℕ // p ∈ P g}) J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux s t then
    originalEdgeScalar
      (if o=1 then sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu
        Q hA hB xi aux s t else
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux t s)
      zeta theta
      (sourceOriginalB26FrozenD434 (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        J ell m dsmall (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux s
        (fun _ => Equiv.refl _)) o k
  else 0

/-- No analytic smallness premise on Knu: its canonical character/cell cap
is proved and inserted into the numerical-history CLEAN BIG Hilbert bound.
The displayed Q/xi cost is real and is not discarded. -/
theorem source_original_B26_CANONICAL_NUMERIC_CLEAN_Hilbert434
    (hi : Function.Injective (fun p : Sigma (fun g => {p : ℕ // p ∈ P g}) => p.2.val))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : G → ℝ) (Q : ℕ) (hA hB xi zeta theta : ℝ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (o k : ℤ) (ho : o=1 ∨ o= -1) (dsmall : ℕ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (keep : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell →
      Finset ℕ → SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Prop)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell mu
      (sourceOriginalB26NumericMarkedClean434 (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        J ell m hmJ nu mu
        (sourceOriginalB26CanonicalNumericCleanK434 J ell m hmJ nu P V Q
          hA hB xi zeta theta o k dsmall aux keep) f) ≤
    ((Q:ℝ)^4*(xi⁻¹)^2)^2 *
      (∏ g : G,((∑ p : {p : ℕ // p ∈ P g},mu g p)^2/4)^
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalB26NumericActiveEnergy434 (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell mu f := by
  apply source_original_B26_NUMERIC_CLEAN_Hilbert434
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    J ell m hmJ nu hi mu hmu _ (by positivity)
  intro s S t
  unfold sourceOriginalB26CanonicalNumericCleanK434
  split_ifs
  · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
    exact source_original_memory_CANONICAL_K_norm434 P V J ell m hmJ nu
      Q hA hB xi hhA hhB hxi aux s t
  · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
    exact source_original_memory_CANONICAL_K_norm434 P V J ell m hmJ nu
      Q hA hB xi hhA hhB hxi aux t s
  · simp only [norm_zero]
    positivity

end Green64Analytic.CorrelationSquare

end

end

