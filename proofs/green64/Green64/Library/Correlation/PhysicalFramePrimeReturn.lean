module

public import Green64.Library.Weights.Part057
public import Green64.Library.Correlation.Part030

@[expose] public section

/-!
# Correlation / PhysicalFramePrimeReturn

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalFramePrimeReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The N+1 true G visits, including BOTH boundary visits; the final
entry has no subsequent E translation. -/
def sourceOriginalPhysicalSourceStepVisits434 (q : ℝ) (N : ℕ) (steps : ℕ → ℤ) :
    List (ℝ × ℤ) :=
  List.ofFn (fun i : Fin (N+1) =>
    (sourceVisitEta q N i,if (i:ℕ)<N then steps i else 0))

theorem source_original_PHYSICAL_SOURCE_STEP_visits_length434
    (q : ℝ) (N : ℕ) (steps : ℕ → ℤ) :
    (sourceOriginalPhysicalSourceStepVisits434 q N steps).length=N+1 := by
  simp [sourceOriginalPhysicalSourceStepVisits434]

theorem source_original_PHYSICAL_SOURCE_STEP_visits_sum434
    (q : ℝ) (N : ℕ) (steps : ℕ → ℤ) :
    ((sourceOriginalPhysicalSourceStepVisits434 q N steps).map Prod.fst).sum =
      ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i := by
  simp only [sourceOriginalPhysicalSourceStepVisits434,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => sourceVisitEta q N i) (N+1)

theorem source_original_PHYSICAL_SOURCE_STEP_visits_unit434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (steps : ℕ → ℤ) :
    ∀ v ∈ sourceOriginalPhysicalSourceStepVisits434 q N steps,0 ≤ v.1 ∧ v.1 ≤ 1 := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact source_original_B26_visit_eta_unit434 q hq hq1 N i

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- Baseline envelope for the literal translated singleton physical G
chain with the original mu-tilde and visit parameters. All algebraic
normalization hypotheses of the abstract return envelope are discharged.
This does not assert tensor extraction from the mixed many-prime chain. -/
theorem source_original_PHYSICAL_SOURCE_SINGLE_PRIME_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (V : BG → ℝ)
    (g : BG) (p : BP g) (hV : V g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP bm q N g p)
    (steps : ℕ → ℤ) (H : Bool → ℂ) (M : ℝ) (hH : ∀ s,‖H s‖ ≤ M) :
    ‖(physicalSourceBaseline BP bm q N g p:ℂ) *
      sourceOriginalPhysicalSinglePrimeChain434 (bm g) p (V g)
        (physicalSourceMuTilde BP bm q N V g)
        (sourceOriginalPhysicalSourceStepVisits434 q N steps)
        (sourceOriginalSinglePrimeVacuumObservation434 (bm g) H) 0 false‖ ≤ M := by
  have hp : (bm g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (bm g p)
  have hlam : V g*physicalSourceMuTilde BP bm q N V g p =
      1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
    unfold physicalSourceMuTilde
    field_simp [hV,hp,ne_of_gt hb]
  have ht := source_original_PHYSICAL_SINGLE_PRIME_baseline_envelope434
    (bm g) p (V g) (physicalSourceMuTilde BP bm q N V g)
    (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
    (source_original_PHYSICAL_SOURCE_STEP_visits_unit434 q hq hq1 N steps)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,
      physicalSourceBaseline] using hb)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,
      physicalSourceBaseline] using hlam) H M hH
  simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using ht

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The single-prime bound with the exact signed E-step schedule of a
complete original frame history. Uniform at every finite N and group
cardinality; no additional threshold depends on the history. -/
theorem source_original_PHYSICAL_FRAME_SINGLE_PRIME_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (V : BG → ℝ)
    (g : BG) (p : BP g) (hV : V g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP bm q N g p)
    (k : ℤ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (H : Bool → ℂ) (M : ℝ) (hH : ∀ s,‖H s‖ ≤ M) :
    ‖(physicalSourceBaseline BP bm q N g p:ℂ) *
      sourceOriginalPhysicalSinglePrimeChain434 (bm g) p (V g)
        (physicalSourceMuTilde BP bm q N V g)
        (sourceOriginalPhysicalSourceStepVisits434 q N
          (fun i => (sourceOriginalFrameHistorySteps434 SP sm BP bm J ell m cap patterns
            k N h 0 y).getD i 0))
        (sourceOriginalSinglePrimeVacuumObservation434 (bm g) H) 0 false‖ ≤ M := by
  exact source_original_PHYSICAL_SOURCE_SINGLE_PRIME_envelope434 BP bm
    q hq hq1 N V g p hV hb _ H M hH
end Green64Analytic.CorrelationSquare

end

end

