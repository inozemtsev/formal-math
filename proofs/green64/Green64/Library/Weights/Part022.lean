module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic
public import Mathlib
public import Green64.Library.Weights.Part001
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Analysis.PrimeNumberTheorem.Part001

@[expose] public section

/-!
# Weights / Part022

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceReverseUnique -/

section

namespace Green64MemoryFinal

theorem source_reverse_unique :
∀ {P : Type} [Fintype P] [DecidableEq P] (V : P → Type) [∀ p, AddCommGroup (V p)] (T : ℕ)
 (A M F G E S K R U : ℕ → Finset P)
 (h rb ra : (i : ℕ) → (p : P) → V p),
 U 0 = ∅ → M 0 = ∅ → F 0 = A 0 →
 (∀ i, F i ⊆ A i ∧ Disjoint (F i) (U i) ∧ Disjoint (G i) (U i ∪ F i) ∧
   E i ⊆ M i ∧ S i ⊆ A i ∧ K i ⊆ A i \ S i ∧ R i ⊆ (M i \ E i) ∪ G i ∧
   A (i+1) = S i ∪ R i ∪ F (i+1) ∧
   M (i+1) = (((M i \ E i) ∪ G i) \ R i) ∪ K i ∧
   U (i+1) = (U i ∪ F i) ∪ G i) →
 (∀ i, T ≤ i → A i = ∅ ∧ M i = ∅ ∧ F i = ∅ ∧ G i = ∅ ∧ U i = U T) →
 (∀ i p,
   (p ∈ G i → ra i p = 0) ∧
   (p ∈ M i \ E i → ra i p = rb i p) ∧
   (p ∈ S i → h (i+1) p = h i p) ∧
   (p ∈ K i → rb (i+1) p = h (i+1) p - h i p) ∧
   (p ∈ R i → ra i p + (h (i+1) p - h i p) = 0) ∧
   (p ∈ ((M i \ E i) ∪ G i) \ R i →
      rb (i+1) p = ra i p + (h (i+1) p - h i p)) ∧
   (p ∈ E i → rb i p = 0)) →
 ∃! life : P → Option (ℕ × ℕ), ∀ p,
   match life p with
   | none => ∀ i, p ∉ A i ∧ p ∉ M i ∧ p ∉ G i
   | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ (az.1 = az.2 → p ∈ A az.1) ∧ (∀ i,
       (p ∈ A i → az.1 ≤ i ∧ i ≤ az.2) ∧
       (p ∈ M i ↔ az.1 < i ∧ i ≤ az.2 ∧ p ∉ A i) ∧
       (p ∈ (M i \ E i) ∪ G i ↔ az.1 ≤ i ∧ i < az.2 ∧ p ∉ A i) ∧
       (p ∈ F i ∪ G i ↔ az.1 = i) ∧
       (p ∈ E i ∪ (A i \ (S i ∪ K i)) ↔ az.2 = i)) ∧
     (∀ i, p ∈ A i → h i p = h az.1 p) ∧
     h az.2 p = h az.1 p ∧
     (∀ i, p ∈ M i → rb i p = h i p - h az.1 p) ∧
     (∀ i, p ∈ (M i \ E i) ∪ G i → ra i p = h i p - h az.1 p) :=
by
  have existence : ∀ {P : Type} [Fintype P] [DecidableEq P] (V : P → Type) [∀ p, AddCommGroup (V p)] (T : ℕ)
 (A M F G E S K R U : ℕ → Finset P)
 (h rb ra : (i : ℕ) → (p : P) → V p),
 U 0 = ∅ → M 0 = ∅ → F 0 = A 0 →
 (∀ i, F i ⊆ A i ∧ Disjoint (F i) (U i) ∧ Disjoint (G i) (U i ∪ F i) ∧
   E i ⊆ M i ∧ S i ⊆ A i ∧ K i ⊆ A i \ S i ∧ R i ⊆ (M i \ E i) ∪ G i ∧
   A (i+1) = S i ∪ R i ∪ F (i+1) ∧
   M (i+1) = (((M i \ E i) ∪ G i) \ R i) ∪ K i ∧
   U (i+1) = (U i ∪ F i) ∪ G i) →
 (∀ i, T ≤ i → A i = ∅ ∧ M i = ∅ ∧ F i = ∅ ∧ G i = ∅ ∧ U i = U T) →
 (∀ i p,
   (p ∈ G i → ra i p = 0) ∧
   (p ∈ M i \ E i → ra i p = rb i p) ∧
   (p ∈ S i → h (i+1) p = h i p) ∧
   (p ∈ K i → rb (i+1) p = h (i+1) p - h i p) ∧
   (p ∈ R i → ra i p + (h (i+1) p - h i p) = 0) ∧
   (p ∈ ((M i \ E i) ∪ G i) \ R i →
      rb (i+1) p = ra i p + (h (i+1) p - h i p)) ∧
   (p ∈ E i → rb i p = 0)) →
 ∃ life : P → Option (ℕ × ℕ), ∀ p,
   match life p with
   | none => ∀ i, p ∉ A i ∧ p ∉ M i ∧ p ∉ G i
   | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ (az.1 = az.2 → p ∈ A az.1) ∧ (∀ i,
       (p ∈ A i → az.1 ≤ i ∧ i ≤ az.2) ∧
       (p ∈ M i ↔ az.1 < i ∧ i ≤ az.2 ∧ p ∉ A i) ∧
       (p ∈ (M i \ E i) ∪ G i ↔ az.1 ≤ i ∧ i < az.2 ∧ p ∉ A i) ∧
       (p ∈ F i ∪ G i ↔ az.1 = i) ∧
       (p ∈ E i ∪ (A i \ (S i ∪ K i)) ↔ az.2 = i)) ∧
     (∀ i, p ∈ A i → h i p = h az.1 p) ∧
     h az.2 p = h az.1 p ∧
     (∀ i, p ∈ M i → rb i p = h i p - h az.1 p) ∧
     (∀ i, p ∈ (M i \ E i) ∪ G i → ra i p = h i p - h az.1 p) :=
    by
      have extract : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
     (A M F G E S K R U : ℕ → Finset P),
     U 0 = ∅ → M 0 = ∅ → F 0 = A 0 →
     (∀ i, F i ⊆ A i ∧ Disjoint (F i) (U i) ∧ Disjoint (G i) (U i ∪ F i) ∧
       E i ⊆ M i ∧ S i ⊆ A i ∧ K i ⊆ A i \ S i ∧ R i ⊆ (M i \ E i) ∪ G i ∧
       A (i+1) = S i ∪ R i ∪ F (i+1) ∧
       M (i+1) = (((M i \ E i) ∪ G i) \ R i) ∪ K i ∧
       U (i+1) = (U i ∪ F i) ∪ G i) →
     (∀ i, T ≤ i → A i = ∅ ∧ M i = ∅ ∧ F i = ∅ ∧ G i = ∅ ∧ U i = U T) →
     ∃ life : P → Option (ℕ × ℕ), ∀ p,
       match life p with
       | none => ∀ i, p ∉ A i ∧ p ∉ M i ∧ p ∉ G i
       | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ (az.1 = az.2 → p ∈ A az.1) ∧ ∀ i,
           (p ∈ A i → az.1 ≤ i ∧ i ≤ az.2) ∧
           (p ∈ M i ↔ az.1 < i ∧ i ≤ az.2 ∧ p ∉ A i) ∧
           (p ∈ (M i \ E i) ∪ G i ↔ az.1 ≤ i ∧ i < az.2 ∧ p ∉ A i) ∧
           (p ∈ F i ∪ G i ↔ az.1 = i) ∧
           (p ∈ E i ∪ (A i \ (S i ∪ K i)) ↔ az.2 = i) :=
        by
          have conserve : ∀ {P : Type} [DecidableEq P] (A M F G E S T R H : Finset P),
         F ⊆ A → Disjoint A M → Disjoint G (A ∪ M) →
         E ⊆ M → S ⊆ A → T ⊆ A \ S → R ⊆ (M \ E) ∪ G →
         Disjoint H (A ∪ M ∪ G) →
         let C := (M \ E) ∪ G;
         let Anext := S ∪ R ∪ H;
         let Mnext := (C \ R) ∪ T;
         let births := F ∪ G;
         let deaths := E ∪ (A \ (S ∪ T));
         let present := (A \ F ∪ M) ∪ births;
         present \ deaths = (Anext \ H) ∪ Mnext ∧
         Disjoint Anext Mnext ∧ deaths ⊆ present ∧
         births ∩ deaths ⊆ A := by
            classical
            intro P _ A M F G E S T R H hFA hAM hGAM hEM hSA hT hR hH
            dsimp only
            have rules (p : P) :
                (p ∈ F → p ∈ A) ∧
                (p ∈ A → p ∉ M) ∧
                (p ∈ G → p ∉ A ∧ p ∉ M) ∧
                (p ∈ E → p ∈ M) ∧
                (p ∈ S → p ∈ A) ∧
                (p ∈ T → p ∈ A ∧ p ∉ S) ∧
                (p ∈ R → (p ∈ M ∧ p ∉ E) ∨ p ∈ G) ∧
                (p ∈ H → p ∉ A ∧ p ∉ M ∧ p ∉ G) := by
              refine ⟨fun hp => hFA hp, fun hp => Finset.disjoint_left.mp hAM hp, ?_,
                fun hp => hEM hp, fun hp => hSA hp, ?_, ?_, ?_⟩
              · intro hp
                have hh := Finset.disjoint_left.mp hGAM hp
                exact ⟨fun h => hh (Finset.mem_union_left _ h), fun h => hh (Finset.mem_union_right _ h)⟩
              · intro hp
                exact Finset.mem_sdiff.mp (hT hp)
              · intro hp
                simpa only [Finset.mem_union,Finset.mem_sdiff] using hR hp
              · intro hp
                have hh := Finset.disjoint_left.mp hH hp
                exact ⟨fun h => hh (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
                  fun h => hh (Finset.mem_union_left _ (Finset.mem_union_right _ h)),
                  fun h => hh (Finset.mem_union_right _ h)⟩
            refine ⟨?_, ?_, ?_, ?_⟩
            · ext p
              have hr := rules p
              simp only [Finset.mem_union, Finset.mem_sdiff]
              rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
              clear rules hFA hAM hGAM hEM hSA hT hR hH
              grind
            · apply Finset.disjoint_left.mpr
              intro p hp hq
              have hr := rules p
              simp only [Finset.mem_union, Finset.mem_sdiff] at hp hq
              rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
              clear rules hFA hAM hGAM hEM hSA hT hR hH
              grind
            · intro p hp
              have hr := rules p
              simp only [Finset.mem_union, Finset.mem_sdiff] at hp ⊢
              rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
              clear rules hFA hAM hGAM hEM hSA hT hR hH
              grind
            · intro p hp
              have hr := rules p
              simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hp
              rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
              clear rules hFA hAM hGAM hEM hSA hT hR hH
              grind
          have extractLife : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
         (U L B D : ℕ → Finset P),
         U 0 = ∅ → L 0 = ∅ →
         (∀ i, D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
           U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i) →
         L T = ∅ →
         (∀ i, T ≤ i → U i = U T ∧ L i = L T ∧ B i = ∅) →
         ∃ life : P → Option (ℕ × ℕ), ∀ p,
           match life p with
           | none => ∀ i, p ∉ L i ∪ B i ∧ p ∉ B i ∧ p ∉ D i
           | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ ∀ i,
               (p ∈ L i ∪ B i ↔ az.1 ≤ i ∧ i ≤ az.2) ∧
               (p ∈ B i ↔ az.1 = i) ∧ (p ∈ D i ↔ az.2 = i) := by
            clear conserve
            have refineClock : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
           (U L B D : ℕ → Finset P),
           U 0 = ∅ → L 0 = ∅ →
           (∀ i, D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
             U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i) →
           L T = ∅ →
           (∀ i, T ≤ i → U i = U T ∧ L i = L T ∧ B i = ∅) →
           let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ 2*T};
           let encode (s : Option Span) (i : ℕ) : ℕ :=
             match s with
             | none => 0
             | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
           ∃ s : P → Option Span, (∀ i p,
             (p ∈ L i ∪ B i ↔ encode (s p) (2*i+1) = 1) ∧
             (p ∈ B i ↔ encode (s p) (2*i) = 0 ∧ encode (s p) (2*i+1) = 1) ∧
             (p ∈ D i ↔ encode (s p) (2*i+1) = 1 ∧ encode (s p) (2*i+2) = 2)) ∧
             ∀ p (bd : Span), s p = some bd → bd.val.1 % 2 = 1 ∧ bd.val.2 % 2 = 0 := by
              have flow : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ),
             let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
             let encode (s : Option Span) (i : ℕ) : ℕ :=
               match s with
               | none => 0
               | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
             let Data := (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P);
             let validFlow (x : Data) : Prop :=
               x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
               (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
                 x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
                 x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
               x.2.1 T = ∅ ∧ (∀ i, T ≤ i → x.1 i = x.1 T ∧ x.2.1 i = x.2.1 T);
             ∃ e : (P → Option Span) ≃ {x : Data // validFlow x},
               ∀ s i p,
                 (p ∈ (e s).val.1 i ↔ encode (s p) i ≠ 0) ∧
                 (p ∈ (e s).val.2.1 i ↔ encode (s p) i = 1) ∧
                 (p ∈ (e s).val.2.2.1 i ↔ encode (s p) i = 0 ∧ encode (s p) (i+1) = 1) ∧
                 (p ∈ (e s).val.2.2.2 i ↔ encode (s p) i = 1 ∧ encode (s p) (i+1) = 2) := by
                have phaseOfEvent : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
               (U L B D : ℕ → Finset P),
               U 0 = ∅ → L 0 = ∅ →
               (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
                 U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) →
               L T = ∅ →
               (∀ i, T ≤ i → U i = U T ∧ L i = L T) →
               let phase (p : P) (i : ℕ) := if p ∈ L i then 1 else if p ∈ U i then 2 else 0;
               (∀ i, L i ⊆ U i) ∧
               (∀ p, phase p 0 = 0 ∧
                 (∀ i, phase p i ≤ phase p (i+1) ∧ phase p (i+1) ≤ phase p i + 1) ∧
                 (∀ i, phase p i ≤ 2) ∧ phase p T ≠ 1 ∧
                 (∀ i, T ≤ i → phase p i = phase p T)) ∧
               (∀ i p, (p ∈ U i ↔ phase p i ≠ 0) ∧ (p ∈ L i ↔ phase p i = 1) ∧
                 (p ∈ B i ↔ phase p i = 0 ∧ phase p (i+1) = 1) ∧
                 (p ∈ D i ↔ phase p i = 1 ∧ phase p (i+1) = 2)) := by
                  classical
                  intro P _ _ T U L B D hU0 hL0 step hLT tail
                  dsimp only
                  let phase (p : P) (i : ℕ) := if p ∈ L i then 1 else if p ∈ U i then 2 else 0
                  have sub : ∀ i, L i ⊆ U i := by
                    intro i
                    induction i with
                    | zero => simp [hU0,hL0]
                    | succ i ih =>
                      intro p hp
                      rw [(step i).2.2.2] at hp
                      rw [(step i).2.2.1]
                      rcases Finset.mem_union.mp hp with hp|hp
                      · exact Finset.mem_union_left _ (ih (Finset.mem_sdiff.mp hp).1)
                      · exact Finset.mem_union_right _ hp
                  have one (i : ℕ) (p : P) :
                      phase p i ≤ phase p (i+1) ∧ phase p (i+1) ≤ phase p i + 1 ∧
                      (p ∈ B i ↔ phase p i = 0 ∧ phase p (i+1) = 1) ∧
                      (p ∈ D i ↔ phase p i = 1 ∧ phase p (i+1) = 2) := by
                    have hd : p ∈ D i → p ∈ L i := fun h => (step i).1 h
                    have hf : p ∈ B i → p ∉ U i := fun h => Finset.disjoint_left.mp (step i).2.1 h
                    have hu : p ∈ U (i+1) ↔ p ∈ U i ∨ p ∈ B i := by rw [(step i).2.2.1]; simp
                    have hl : p ∈ L (i+1) ↔ (p ∈ L i ∧ p ∉ D i) ∨ p ∈ B i := by
                      rw [(step i).2.2.2]; simp
                    have hsub : p ∈ L i → p ∈ U i := fun h => sub i h
                    try dsimp [phase]
                    by_cases h1 : p ∈ L i <;> by_cases h2 : p ∈ U i <;>
                      by_cases h3 : p ∈ B i <;> by_cases h4 : p ∈ D i <;>
                      simp_all
                  refine ⟨sub, ?_, ?_⟩
                  · intro p
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · simp [phase, hU0, hL0]
                    · intro i
                      exact ⟨(one i p).1, (one i p).2.1⟩
                    · intro i
                      try dsimp [phase]
                      split_ifs <;> omega
                    · simp [hLT]
                      split_ifs <;> norm_num
                    · intro i hi
                      rw [(tail i hi).1, (tail i hi).2]
                  · intro i p
                    refine ⟨?_, ?_, (one i p).2.2.1, (one i p).2.2.2⟩
                    · have hh : p ∈ L i → p ∈ U i := fun h => sub i h
                      try dsimp [phase]
                      split_ifs <;> simp_all
                    · try dsimp [phase]
                      split_ifs <;> simp_all
                have eventOfPhase : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
               (f : P → ℕ → ℕ),
               (∀ p, f p 0 = 0 ∧
                 (∀ i, f p i ≤ f p (i+1) ∧ f p (i+1) ≤ f p i + 1) ∧
                 (∀ i, f p i ≤ 2) ∧ f p T ≠ 1 ∧ (∀ i, T ≤ i → f p i = f p T)) →
               let U (i : ℕ) := Finset.univ.filter (fun p => f p i ≠ 0);
               let L (i : ℕ) := Finset.univ.filter (fun p => f p i = 1);
               let B (i : ℕ) := Finset.univ.filter (fun p => f p i = 0 ∧ f p (i+1) = 1);
               let D (i : ℕ) := Finset.univ.filter (fun p => f p i = 1 ∧ f p (i+1) = 2);
               U 0 = ∅ ∧ L 0 = ∅ ∧
               (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
                 U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) ∧
               L T = ∅ ∧ (∀ i, T ≤ i → U i = U T ∧ L i = L T) ∧
               (∀ p i, (if p ∈ L i then 1 else if p ∈ U i then 2 else 0) = f p i) := by
                  classical
                  intro P _ _ T f hf
                  dsimp only
                  let U (i : ℕ) := Finset.univ.filter (fun p => f p i ≠ 0)
                  let L (i : ℕ) := Finset.univ.filter (fun p => f p i = 1)
                  let B (i : ℕ) := Finset.univ.filter (fun p => f p i = 0 ∧ f p (i+1) = 1)
                  let D (i : ℕ) := Finset.univ.filter (fun p => f p i = 1 ∧ f p (i+1) = 2)
                  change U 0 = ∅ ∧ L 0 = ∅ ∧
                    (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
                      U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) ∧
                    L T = ∅ ∧ (∀ i, T ≤ i → U i = U T ∧ L i = L T) ∧
                    (∀ p i, (if p ∈ L i then 1 else if p ∈ U i then 2 else 0) = f p i)
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                  · ext p
                    simp [U, (hf p).1]
                  · ext p
                    simp [L, (hf p).1]
                  · intro i
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · intro p hp
                      simp only [D,L,Finset.mem_filter,Finset.mem_univ,true_and] at *
                      exact hp.1
                    · apply Finset.disjoint_left.mpr
                      intro p hp hq
                      simp only [B,U,Finset.mem_filter,Finset.mem_univ,true_and] at *
                      exact hq hp.1
                    · ext p
                      simp only [U,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
                      have hstep := (hf p).2.1 i
                      omega
                    · ext p
                      simp only [L,B,D,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
                      have hstep := (hf p).2.1 i
                      have hbi := (hf p).2.2.1 i
                      have hbn := (hf p).2.2.1 (i+1)
                      omega
                  · ext p
                    simp [L, (hf p).2.2.2.1]
                  · intro i hi
                    constructor <;> ext p <;>
                      simp [U,L, (hf p).2.2.2.2 i hi]
                  · intro p i
                    simp only [L,U,Finset.mem_filter,Finset.mem_univ,true_and]
                    have hb := (hf p).2.2.1 i
                    split_ifs <;> omega
                have simultaneous : ∀ (P : Type) (T : ℕ),
               let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
               let valid (f : ℕ → ℕ) : Prop :=
                 f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
                 (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T);
               let encode (s : Option Span) (i : ℕ) : ℕ :=
                 match s with
                 | none => 0
                 | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
               ∃ e : (P → Option Span) ≃ {f : P → ℕ → ℕ // ∀ p, valid (f p)},
                 ∀ s p i, (e s).val p i = encode (s p) i := by
                  have scalar : ∀ (T : ℕ),
                 let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
                 let valid (f : ℕ → ℕ) : Prop :=
                   f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
                   (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T);
                 let encode (s : Option Span) (i : ℕ) : ℕ :=
                   match s with
                   | none => 0
                   | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
                 (∀ s, valid (encode s)) ∧
                 (∀ f, valid f → ∃! s, encode s = f) := by
                    have interval : ∀ (T : ℕ) (f : ℕ → ℕ),
                   f 0 = 0 →
                   (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) →
                   (∀ i, f i ≤ 2) →
                   f T = 2 →
                   ∃ b d : ℕ, 0 < b ∧ b < d ∧ d ≤ T ∧
                     (∀ i, f i = if i < b then 0 else if i < d then 1 else 2) ∧
                     (∀ b' d', 0 < b' → b' < d' → d' ≤ T →
                       (∀ i, f i = if i < b' then 0 else if i < d' then 1 else 2) →
                         b' = b ∧ d' = d) := by
                      intro T f h0 hs hb hT
                      have mono : Monotone f := monotone_nat_of_le_succ (fun i => (hs i).1)
                      have exb : ∃ i, 1 ≤ f i := ⟨T, by omega⟩
                      have exd : ∃ i, 2 ≤ f i := ⟨T, by omega⟩
                      let b := Nat.find exb
                      let d := Nat.find exd
                      have fb : 1 ≤ f b := Nat.find_spec exb
                      have fd : 2 ≤ f d := Nat.find_spec exd
                      have db : d ≤ T := Nat.find_min' exd (by omega)
                      have bpos : 0 < b := by
                        by_contra h
                        have : b = 0 := by omega
                        rw [this, h0] at fb
                        omega
                      have pre_b : ∀ i, i < b → f i = 0 := by
                        intro i hi
                        have : ¬ 1 ≤ f i := Nat.find_min exb hi
                        omega
                      have pre_d : ∀ i, i < d → f i ≤ 1 := by
                        intro i hi
                        have : ¬ 2 ≤ f i := Nat.find_min exd hi
                        omega
                      have fb1 : f b = 1 := by
                        have hprev := pre_b (b-1) (by omega)
                        have hstep := (hs (b-1)).2
                        have he : b-1+1 = b := by omega
                        rw [he, hprev] at hstep
                        omega
                      have bd : b < d := by
                        by_contra h
                        have hmono := mono (show d ≤ b by omega)
                        omega
                      have shape : ∀ i, f i = if i < b then 0 else if i < d then 1 else 2 := by
                        intro i
                        by_cases hi : i < b
                        · simp [hi, pre_b i hi]
                        · by_cases hd : i < d
                          · have hmono := mono (show b ≤ i by omega)
                            have hupper := pre_d i hd
                            simp only [hi, hd, if_false, if_true]
                            omega
                          · have hmono := mono (show d ≤ i by omega)
                            have hupper := hb i
                            simp only [hi, hd, if_false]
                            omega
                      refine ⟨b, d, bpos, bd, db, shape, ?_⟩
                      intro b' d' hb' hbd' hd' shape'
                      have bb : b' = b := by
                        have h1 := shape b
                        have h2 := shape' b
                        have h3 := shape b'
                        have h4 := shape' b'
                        split_ifs at h1 h2 h3 h4 <;> omega
                      subst b'
                      have dd : d' = d := by
                        have h1 := shape d
                        have h2 := shape' d
                        have h3 := shape d'
                        have h4 := shape' d'
                        split_ifs at h1 h2 h3 h4 <;> omega
                      exact ⟨rfl, dd⟩
                    intro T
                    dsimp only
                    let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
                    let valid (f : ℕ → ℕ) : Prop :=
                      f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
                      (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
                    let encode (s : Option Span) (i : ℕ) : ℕ :=
                      match s with
                      | none => 0
                      | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
                    change (∀ s, valid (encode s)) ∧ (∀ f, valid f → ∃! s, encode s = f)
                    have encvalid : ∀ s, valid (encode s) := by
                      intro s
                      cases s with
                      | none => simp [valid, encode]
                      | some bd =>
                        rcases bd with ⟨⟨b,d⟩, hb, hbd, hd⟩
                        dsimp [valid, encode]
                        refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · simp [hb]
                        · intro i
                          split_ifs <;> omega
                        · intro i
                          split_ifs <;> omega
                        · split_ifs <;> omega
                        · intro i hi
                          split_ifs <;> omega
                    refine ⟨encvalid, ?_⟩
                    intro f hf
                    rcases hf with ⟨h0, hs, hb, hv, htail⟩
                    have mono : Monotone f := monotone_nat_of_le_succ (fun i => (hs i).1)
                    by_cases ht : f T = 0
                    · have hfzero : f = fun _ => 0 := by
                        funext i
                        by_cases hi : i ≤ T
                        · have := mono hi
                          omega
                        · rw [htail i (by omega), ht]
                      refine ⟨none, ?_, ?_⟩
                      · exact hfzero.symm
                      · intro s he
                        cases s with
                        | none => rfl
                        | some bd =>
                          have ee := congrFun he bd.val.1
                          have hh := congrFun hfzero bd.val.1
                          have hbd := bd.property.2.1
                          simp [encode, hbd] at ee
                          omega
                    · have ht2 : f T = 2 := by have := hb T; omega
                      obtain ⟨b,d,hbp,hbd,hd,shape,uniq⟩ := interval T f h0 hs hb ht2
                      let bd : Span := ⟨(b,d),hbp,hbd,hd⟩
                      refine ⟨some bd, ?_, ?_⟩
                      · funext i
                        exact (shape i).symm
                      · intro s he
                        cases s with
                        | none =>
                          have ee := congrFun he T
                          change 0 = f T at ee
                          omega
                        | some bd' =>
                          have shp : ∀ i, f i = if i < bd'.val.1 then 0 else if i < bd'.val.2 then 1 else 2 := by
                            intro i
                            exact (congrFun he i).symm
                          obtain ⟨e1,e2⟩ := uniq bd'.val.1 bd'.val.2 bd'.property.1 bd'.property.2.1 bd'.property.2.2 shp
                          congr 1
                          apply Subtype.ext
                          exact Prod.ext e1 e2
                  classical
                  intro P T
                  dsimp only
                  let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
                  let valid (f : ℕ → ℕ) : Prop :=
                    f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
                    (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
                  let encode (s : Option Span) (i : ℕ) : ℕ :=
                    match s with
                    | none => 0
                    | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
                  let Tr := {f : P → ℕ → ℕ // ∀ p, valid (f p)}
                  have hscalar : (∀ s, valid (encode s)) ∧ (∀ f, valid f → ∃! s, encode s = f) := scalar T
                  let forward (s : P → Option Span) : Tr :=
                    ⟨fun p => encode (s p), fun p => hscalar.1 (s p)⟩
                  have hi : Function.Injective forward := by
                    intro s t h
                    funext p
                    have hs := hscalar.2 (encode (s p)) (hscalar.1 (s p))
                    obtain ⟨u,hu,huniq⟩ := hs
                    have hst : encode (t p) = encode (s p) := by
                      exact (congrFun (congrArg Subtype.val h) p).symm
                    exact (huniq (s p) rfl).trans (huniq (t p) hst).symm
                  have hs : Function.Surjective forward := by
                    intro f
                    choose s h using fun p => (hscalar.2 (f.val p) (f.property p)).exists
                    refine ⟨s, ?_⟩
                    apply Subtype.ext
                    funext p
                    exact h p
                  refine ⟨Equiv.ofBijective forward ⟨hi,hs⟩, ?_⟩
                  intro s p i
                  rfl
                classical
                intro P _ _ T
                dsimp only
                let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
                let encode (s : Option Span) (i : ℕ) : ℕ :=
                  match s with
                  | none => 0
                  | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
                let valid (f : ℕ → ℕ) : Prop :=
                  f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
                  (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
                let Trace := {f : P → ℕ → ℕ // ∀ p, valid (f p)}
                let Data := (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P)
                let validFlow (x : Data) : Prop :=
                  x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
                  (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
                    x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
                    x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
                  x.2.1 T = ∅ ∧ (∀ i, T ≤ i → x.1 i = x.1 T ∧ x.2.1 i = x.2.1 T)
                let Flow := {x : Data // validFlow x}
                let toFlow (f : Trace) : Flow :=
                  ⟨(fun i => Finset.univ.filter (fun p => f.val p i ≠ 0),
                    fun i => Finset.univ.filter (fun p => f.val p i = 1),
                    fun i => Finset.univ.filter (fun p => f.val p i = 0 ∧ f.val p (i+1) = 1),
                    fun i => Finset.univ.filter (fun p => f.val p i = 1 ∧ f.val p (i+1) = 2)), by
                      have h := eventOfPhase T f.val f.property
                      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩⟩
                let toTrace (x : Flow) : Trace :=
                  ⟨fun p i => if p ∈ x.val.2.1 i then 1 else if p ∈ x.val.1 i then 2 else 0, by
                    have h := phaseOfEvent T x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2
                      x.property.1 x.property.2.1 x.property.2.2.1 x.property.2.2.2.1 x.property.2.2.2.2
                    exact h.2.1⟩
                have left : ∀ f, toTrace (toFlow f) = f := by
                  intro f
                  apply Subtype.ext
                  funext p i
                  exact (eventOfPhase T f.val f.property).2.2.2.2.2 p i
                have right : ∀ x, toFlow (toTrace x) = x := by
                  intro x
                  have h := (phaseOfEvent T x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2
                    x.property.1 x.property.2.1 x.property.2.2.1 x.property.2.2.2.1 x.property.2.2.2.2).2.2
                  apply Subtype.ext
                  apply Prod.ext
                  · funext i
                    ext p
                    simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).1.symm
                  · apply Prod.ext
                    · funext i
                      ext p
                      simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.1.symm
                    · apply Prod.ext
                      · funext i
                        ext p
                        simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.2.1.symm
                      · funext i
                        ext p
                        simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.2.2.symm
                let tf : Trace ≃ Flow := {toFun := toFlow, invFun := toTrace, left_inv := left, right_inv := right}
                obtain ⟨st,hst⟩ := simultaneous P T
                refine ⟨st.trans tf, ?_⟩
                intro s i p
                change (p ∈ (toFlow (st s)).val.1 i ↔ encode (s p) i ≠ 0) ∧
                  (p ∈ (toFlow (st s)).val.2.1 i ↔ encode (s p) i = 1) ∧
                  (p ∈ (toFlow (st s)).val.2.2.1 i ↔ encode (s p) i = 0 ∧ encode (s p) (i+1) = 1) ∧
                  (p ∈ (toFlow (st s)).val.2.2.2 i ↔ encode (s p) i = 1 ∧ encode (s p) (i+1) = 2)
                simp [toFlow, hst, encode]
                exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩
              classical
              intro P _ _ T U L B D hU hL hlocal hLT htail
              dsimp only
              let UU (i : ℕ) := if i%2=0 then U (i/2) else U (i/2) ∪ B (i/2)
              let LL (i : ℕ) := if i%2=0 then L (i/2) else L (i/2) ∪ B (i/2)
              let BB (i : ℕ) := if i%2=0 then B (i/2) else ∅
              let DD (i : ℕ) := if i%2=0 then ∅ else D (i/2)
              have even (i : ℕ) :
                  UU (2*i) = U i ∧ LL (2*i) = L i ∧ BB (2*i) = B i ∧ DD (2*i) = ∅ := by
                simp [UU, LL, BB, DD]
              have odd (i : ℕ) :
                  UU (2*i+1) = U i ∪ B i ∧ LL (2*i+1) = L i ∪ B i ∧
                  BB (2*i+1) = ∅ ∧ DD (2*i+1) = D i := by
                have hd : (2*i+1)/2=i := by omega
                have hm : (2*i+1)%2=1 := by omega
                simp [UU, LL, BB, DD, hd, hm]
              have hstep (i : ℕ) : DD i ⊆ LL i ∧ Disjoint (BB i) (UU i) ∧
                  UU (i+1) = UU i ∪ BB i ∧ LL (i+1) = (LL i \ DD i) ∪ BB i := by
                by_cases hi : i%2=0
                · obtain ⟨j,rfl⟩ : ∃ j, i=2*j := ⟨i/2,by omega⟩
                  rw [(even j).1, (even j).2.1, (even j).2.2.1, (even j).2.2.2,
                    (odd j).1, (odd j).2.1]
                  simp [(hlocal j).2.1]
                · obtain ⟨j,rfl⟩ : ∃ j, i=2*j+1 := ⟨i/2,by omega⟩
                  have he : 2*j+1+1=2*(j+1) := by omega
                  rw [he, (even (j+1)).1, (even (j+1)).2.1,
                    (odd j).1, (odd j).2.1, (odd j).2.2.1, (odd j).2.2.2]
                  simp [(hlocal j).1, (hlocal j).2.2.1, (hlocal j).2.2.2]
              have htail' (i : ℕ) (hi : 2*T ≤ i) : UU i = UU (2*T) ∧ LL i = LL (2*T) := by
                have hj : T ≤ i/2 := by omega
                have ht := htail (i/2) hj
                rw [(even T).1, (even T).2.1]
                simp [UU, LL, ht.1, ht.2.1, ht.2.2]
              obtain ⟨e,he⟩ := flow (P:=P) (2*T)
              let x := (UU,LL,BB,DD)
              have hx : x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
                  (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
                    x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
                    x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
                  x.2.1 (2*T) = ∅ ∧
                  (∀ i, 2*T ≤ i → x.1 i = x.1 (2*T) ∧ x.2.1 i = x.2.1 (2*T)) :=
                ⟨by simpa [x,UU] using hU, by simpa [x,LL] using hL, hstep,
                 by change LL (2*T) = ∅; exact (even T).2.1.trans hLT, htail'⟩
              let s := e.symm ⟨x,hx⟩
              have hs : e s = ⟨x,hx⟩ := e.apply_symm_apply _
              refine ⟨s, ?_, ?_⟩
              · intro i p
                have ho := he s (2*i+1) p
                have hev := he s (2*i) p
                rw [hs] at ho hev
                change (p ∈ UU (2*i+1) ↔ _) ∧ (p ∈ LL (2*i+1) ↔ _) ∧
                  (p ∈ BB (2*i+1) ↔ _) ∧ (p ∈ DD (2*i+1) ↔ _) at ho
                change (p ∈ UU (2*i) ↔ _) ∧ (p ∈ LL (2*i) ↔ _) ∧
                  (p ∈ BB (2*i) ↔ _) ∧ (p ∈ DD (2*i) ↔ _) at hev
                rw [(odd i).2.1, (odd i).2.2.2] at ho
                rw [(even i).2.2.1] at hev
                exact ⟨ho.2.1,hev.2.2.1,ho.2.2.2⟩
              · intro p bd hp
                obtain ⟨hbpos,hbd,hdT⟩ := bd.property
                have hb := (he s (bd.val.1-1) p).2.2.1
                have hd := (he s (bd.val.2-1) p).2.2.2
                rw [hs] at hb hd
                have hbm : p ∈ BB (bd.val.1-1) := by
                  apply hb.mpr
                  simp only [hp]
                  split_ifs <;> omega
                have hdm : p ∈ DD (bd.val.2-1) := by
                  apply hd.mpr
                  simp only [hp]
                  split_ifs <;> omega
                have hbmod : (bd.val.1-1)%2=0 := by
                  by_contra h
                  simpa [BB,h] using hbm
                have hdmod : (bd.val.2-1)%2≠0 := by
                  intro h
                  simpa [DD,h] using hdm
                omega
            classical
            intro P _ _ T U L B D hU hL hlocal hLT htail
            obtain ⟨s,hs,hpar⟩ := refineClock T U L B D hU hL hlocal hLT htail
            let life (p : P) : Option (ℕ × ℕ) :=
              (s p).map (fun bd => (bd.val.1 / 2, (bd.val.2-1)/2))
            refine ⟨life, ?_⟩
            intro p
            cases hp : s p with
            | none =>
              simp only [life, hp, Option.map_none]
              intro i
              have hh := hs i p
              simpa [hp] using hh
            | some bd =>
              simp only [life, hp, Option.map_some]
              obtain ⟨hbpos,hbd,hdT⟩ := bd.property
              obtain ⟨hbmod,hdmod⟩ := hpar p bd hp
              refine ⟨by omega,by omega,?_⟩
              intro i
              have hh := hs i p
              simp only [hp] at hh
              constructor
              · rw [hh.1]
                split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
              · constructor
                · rw [hh.2.1]
                  split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
                · rw [hh.2.2]
                  split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
          classical
          intro P _ _ T A M F G E S K R U hU0 hM0 hF0 rows tail
          have prep (i : ℕ) (hu : A i \ F i ∪ M i ⊆ U i) :
              A i ∪ M i ∪ G i ⊆ U (i+1) ∧
              Disjoint (G i) (A i ∪ M i) ∧
              Disjoint (F (i+1)) (A i ∪ M i ∪ G i) := by
            rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
            have hsub : A i ∪ M i ⊆ U i ∪ F i := by
              intro p hp
              rcases Finset.mem_union.mp hp with ha | hm
              · by_cases hf : p ∈ F i
                · exact Finset.mem_union_right _ hf
                · exact Finset.mem_union_left _ (hu (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha,hf⟩)))
              · exact Finset.mem_union_left _ (hu (Finset.mem_union_right _ hm))
            have hAll : A i ∪ M i ∪ G i ⊆ U (i+1) := by
              rw [hUn]
              exact Finset.union_subset_union_left hsub
            refine ⟨hAll, ?_, ?_⟩
            · apply Finset.disjoint_left.mpr
              intro p hg hp
              exact Finset.disjoint_left.mp hGU hg (hsub hp)
            · apply Finset.disjoint_left.mpr
              intro p hf hp
              exact Finset.disjoint_left.mp (rows (i+1)).2.1 hf (hAll hp)
          have invariant (i : ℕ) : Disjoint (A i) (M i) ∧ A i \ F i ∪ M i ⊆ U i := by
            induction i with
            | zero => simp [hM0,hF0]
            | succ i ih =>
              rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
              obtain ⟨hAll,hG,hH⟩ := prep i ih.2
              have hc := conserve (A i) (M i) (F i) (G i) (E i) (S i) (K i) (R i) (F (i+1))
                hFA ih.1 hG hEM hSA hK hR hH
              constructor
              · rw [hAn,hMn]
                exact hc.2.1
              · have hC : (M i \ E i) ∪ G i ⊆ U (i+1) := by
                  intro p hp
                  apply hAll
                  rcases Finset.mem_union.mp hp with hm | hg
                  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mp hm).1)
                  · exact Finset.mem_union_right _ hg
                have hAu : A i ⊆ U (i+1) := by
                  intro p hp
                  exact hAll (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
                intro p hp
                rw [hAn,hMn] at hp
                simp only [Finset.mem_union,Finset.mem_sdiff] at hp
                rcases hp with ⟨hp,hn⟩ | hp
                · rcases hp with (hs | hr) | hf
                  · exact hAu (hSA hs)
                  · exact hC (hR hr)
                  · exact False.elim (hn hf)
                · rcases hp with ⟨hp,_⟩ | hk
                  · exact hC (by simpa only [Finset.mem_union,Finset.mem_sdiff] using hp)
                  · exact hAu (Finset.mem_sdiff.mp (hK hk)).1
          let L (i : ℕ) := A i \ F i ∪ M i
          let B (i : ℕ) := F i ∪ G i
          let D (i : ℕ) := E i ∪ (A i \ (S i ∪ K i))
          have hcon (i : ℕ) :
              (L i ∪ B i) \ D i = L (i+1) ∧
              D i ⊆ L i ∪ B i ∧ B i ∩ D i ⊆ A i := by
            rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
            obtain ⟨_,hG,hH⟩ := prep i (invariant i).2
            have hc := conserve (A i) (M i) (F i) (G i) (E i) (S i) (K i) (R i) (F (i+1))
              hFA (invariant i).1 hG hEM hSA hK hR hH
            refine ⟨?_,hc.2.2.1,hc.2.2.2⟩
            change _ = A (i+1) \ F (i+1) ∪ M (i+1)
            rw [hAn,hMn]
            exact hc.1
          have hlocalSource (i : ℕ) : D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
              U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i := by
            rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
            refine ⟨(hcon i).2.1, ?_, ?_, (hcon i).1.symm⟩
            · apply Finset.disjoint_left.mpr
              intro p hp hu
              rcases Finset.mem_union.mp hp with hf | hg
              · exact Finset.disjoint_left.mp hFU hf hu
              · exact Finset.disjoint_left.mp hGU hg (Finset.mem_union_left _ hu)
            · rw [hUn]
              exact Finset.union_assoc _ _ _
          have hL0 : L 0 = ∅ := by simp [L,hF0,hM0]
          have hLT : L T = ∅ := by
            have ht := tail T le_rfl
            simp [L,ht.1,ht.2.1]
          have htail (i : ℕ) (hi : T ≤ i) : U i = U T ∧ L i = L T ∧ B i = ∅ := by
            have ht := tail i hi
            simp [L,B,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,hLT]
          obtain ⟨life,hlife⟩ := extractLife T U L B D hU0 hL0 hlocalSource hLT htail
          have hAQ (i : ℕ) : A i ⊆ L i ∪ B i := by
            intro p hp
            by_cases hf : p ∈ F i
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ hf)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,hf⟩))
          have hMchar (i : ℕ) (p : P) :
              (p ∈ M i ↔ p ∈ L i ∪ B i ∧ p ∉ A i ∧ p ∉ B i) ∧
              (p ∈ (M i \ E i) ∪ G i ↔ p ∈ L i ∪ B i ∧ p ∉ A i ∧ p ∉ D i) := by
            have hF : p ∈ F i → p ∈ A i := fun hp => (rows i).1 hp
            have hA : p ∈ A i → p ∉ M i := fun hp => Finset.disjoint_left.mp (invariant i).1 hp
            have hG : p ∈ G i → p ∉ A i ∧ p ∉ M i := by
              intro hp
              have hh := Finset.disjoint_left.mp (prep i (invariant i).2).2.1 hp
              exact ⟨fun h => hh (Finset.mem_union_left _ h),fun h => hh (Finset.mem_union_right _ h)⟩
            have hE : p ∈ E i → p ∈ M i := fun hp => (rows i).2.2.2.1 hp
            simp only [L,B,D,Finset.mem_union,Finset.mem_sdiff]
            clear rows prep invariant hcon hlocalSource hlife hAQ htail hLT hL0 tail
            tauto
          refine ⟨life, ?_⟩
          intro p
          have hp := hlife p
          cases hspan : life p with
          | none =>
            simp only [hspan] at hp ⊢
            intro i
            have hq := (hp i).1
            refine ⟨fun ha => hq (hAQ i ha), ?_, ?_⟩
            · intro hm
              exact hq (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
            · intro hg
              exact hq (Finset.mem_union_right _ (Finset.mem_union_right _ hg))
          | some az =>
            simp only [hspan] at hp ⊢
            refine ⟨hp.1,hp.2.1,?_,?_⟩
            · intro haz
              apply (hcon az.1).2.2
              exact Finset.mem_inter.mpr
                ⟨(hp.2.2 az.1).2.1.mpr rfl,(hp.2.2 az.1).2.2.mpr haz.symm⟩
            · intro i
              have hh := hp.2.2 i
              refine ⟨fun ha => hh.1.mp (hAQ i ha), ?_, ?_, hh.2.1,hh.2.2⟩
              · rw [(hMchar i p).1,hh.1,hh.2.1]
                by_cases ha : p ∈ A i
                · simp [ha]
                · simp only [ha,not_false_eq_true,true_and,and_true]
                  omega
              · rw [(hMchar i p).2,hh.1,hh.2.2]
                by_cases ha : p ∈ A i
                · simp [ha]
                · simp only [ha,not_false_eq_true,true_and,and_true]
                  omega
      have reverse : ∀ {R : Type} [AddCommGroup R] (A : ℕ → Prop) (a z : ℕ)
     (h rb ra : ℕ → R),
     a ≤ z →
     (a = z → A a) →
     (∀ i, a ≤ i → i < z → ¬ A i →
       ra i = if i = a then 0 else rb i) →
     (∀ i, a ≤ i → i < z → A i → A (i+1) →
       h (i+1) = h i) →
     (∀ i, a ≤ i → i < z → A i → ¬ A (i+1) →
       rb (i+1) = h (i+1) - h i) →
     (∀ i, a ≤ i → i < z → ¬ A i → A (i+1) →
       ra i + (h (i+1) - h i) = 0) →
     (∀ i, a ≤ i → i < z → ¬ A i → ¬ A (i+1) →
       rb (i+1) = ra i + (h (i+1) - h i)) →
     (¬ A z → rb z = 0) →
     (∀ i, a ≤ i → i ≤ z → A i → h i = h a) ∧
     (∀ i, a < i → i ≤ z → ¬ A i → rb i = h i - h a) ∧
     (∀ i, a ≤ i → i < z → ¬ A i → ra i = h i - h a) ∧
     h z = h a :=
        by
          classical
          intro R _ A a z h rb ra haz hsingle hg hshare hstore hprom hcont hend
          have inv (n : ℕ) : a+n ≤ z →
              (A (a+n) → h (a+n) = h a) ∧
              (a < a+n → ¬ A (a+n) → rb (a+n) = h (a+n) - h a) := by
            induction n with
            | zero =>
              intro _
              constructor
              · intro _; simp
              · intro hh; omega
            | succ n ih =>
              intro hle
              have hi := ih (by omega)
              have ha : a ≤ a+n := by omega
              have hz : a+n < z := by omega
              have hr (hna : ¬ A (a+n)) : ra (a+n) = h (a+n) - h a := by
                rw [hg (a+n) ha hz hna]
                split_ifs with he
                · simp [he]
                · exact hi.2 (by omega) hna
              constructor
              · intro hn
                change h (a+n+1) = h a
                have hn' : A (a+n+1) := hn
                by_cases hp : A (a+n)
                · exact (hshare (a+n) ha hz hp hn').trans (hi.1 hp)
                · apply sub_eq_zero.mp
                  calc
                    h (a+n+1) - h a =
                        ra (a+n) + (h (a+n+1) - h (a+n)) := by rw [hr hp]; abel
                    _ = 0 := hprom (a+n) ha hz hp hn'
              · intro _ hn
                change rb (a+n+1) = h (a+n+1) - h a
                have hn' : ¬ A (a+n+1) := hn
                by_cases hp : A (a+n)
                · rw [hstore (a+n) ha hz hp hn', hi.1 hp]
                · rw [hcont (a+n) ha hz hp hn', hr hp]
                  abel
          have inv' (i : ℕ) (ha : a ≤ i) (hz : i ≤ z) :
              (A i → h i = h a) ∧
              (a < i → ¬ A i → rb i = h i - h a) := by
            have he : a + (i-a) = i := by omega
            have hv := inv (i-a) (by omega)
            simpa only [he] using hv
          have hc (i : ℕ) (ha : a ≤ i) (hz : i ≤ z) (hi : A i) :
              h i = h a := (inv' i ha hz).1 hi
          have hb (i : ℕ) (ha : a < i) (hz : i ≤ z) (hi : ¬ A i) :
              rb i = h i - h a := (inv' i (by omega) hz).2 ha hi
          have hf (i : ℕ) (ha : a ≤ i) (hz : i < z) (hi : ¬ A i) :
              ra i = h i - h a := by
            rw [hg i ha hz hi]
            split_ifs with he
            · simp [he]
            · exact hb i (by omega) (by omega) hi
          refine ⟨hc, hb, hf, ?_⟩
          by_cases hz : A z
          · exact hc z haz (by omega) hz
          · have hlt : a < z := by
              by_contra hn
              have he : a = z := by omega
              exact hz (he ▸ hsingle he)
            exact sub_eq_zero.mp ((hb z hlt (by omega) hz).symm.trans (hend hz))
      classical
      intro P _ _ V _ T A M F G E S K R U h rb ra hU hM hF rows tail residues
      obtain ⟨life, hlife⟩ := extract T A M F G E S K R U hU hM hF rows tail
      refine ⟨life, ?_⟩
      intro p
      have hp := hlife p
      cases hs : life p with
      | none =>
        simpa only [hs] using hp
      | some az =>
        simp only [hs] at hp ⊢
        obtain ⟨haz, hzT, hsingle, supp⟩ := hp
        have notfresh (i : ℕ) (ha : az.1 ≤ i) : p ∉ F (i+1) := by
          intro hf
          have he := (supp (i+1)).2.2.2.1.mp (Finset.mem_union_left _ hf)
          omega
        have notC (i : ℕ) (hi : p ∈ A i) : p ∉ (M i \ E i) ∪ G i := by
          intro hc
          exact ((supp i).2.2.1.mp hc).2.2 hi
        have hg (i : ℕ) (ha : az.1 ≤ i) (hz : i < az.2) (hn : p ∉ A i) :
            ra i p = if i = az.1 then 0 else rb i p := by
          have hc := (supp i).2.2.1.mpr ⟨ha,hz,hn⟩
          by_cases he : i = az.1
          · have hb := (supp i).2.2.2.1.mpr he.symm
            have hghost : p ∈ G i := by
              rcases Finset.mem_union.mp hb with hf | hgg
              · exact False.elim (hn ((rows i).1 hf))
              · exact hgg
            simp only [if_pos he]
            exact (residues i p).1 hghost
          · have hghost : p ∉ G i := by
              intro hgg
              exact he ((supp i).2.2.2.1.mp (Finset.mem_union_right _ hgg)).symm
            have hm : p ∈ M i \ E i := by
              rcases Finset.mem_union.mp hc with hh | hh
              · exact hh
              · exact False.elim (hghost hh)
            simp only [if_neg he]
            exact (residues i p).2.1 hm
        have hshare (i : ℕ) (ha : az.1 ≤ i) (_hz : i < az.2)
            (hi : p ∈ A i) (hn : p ∈ A (i+1)) : h (i+1) p = h i p := by
          have hnext := (rows i).2.2.2.2.2.2.2.1
          rw [hnext] at hn
          rcases Finset.mem_union.mp hn with hn | hf
          · rcases Finset.mem_union.mp hn with hss | hr
            · exact (residues i p).2.2.1 hss
            · exact False.elim (notC i hi ((rows i).2.2.2.2.2.2.1 hr))
          · exact False.elim (notfresh i ha hf)
        have hstore (i : ℕ) (ha : az.1 ≤ i) (hz : i < az.2)
            (hi : p ∈ A i) (hn : p ∉ A (i+1)) :
            rb (i+1) p = h (i+1) p - h i p := by
          have hm := (supp (i+1)).2.1.mpr ⟨by omega,by omega,hn⟩
          rw [(rows i).2.2.2.2.2.2.2.2.1] at hm
          rcases Finset.mem_union.mp hm with hc | hk
          · exact False.elim (notC i hi (Finset.mem_sdiff.mp hc).1)
          · exact (residues i p).2.2.2.1 hk
        have hprom (i : ℕ) (ha : az.1 ≤ i) (_hz : i < az.2)
            (hi : p ∉ A i) (hn : p ∈ A (i+1)) :
            ra i p + (h (i+1) p - h i p) = 0 := by
          rw [(rows i).2.2.2.2.2.2.2.1] at hn
          rcases Finset.mem_union.mp hn with hn | hf
          · rcases Finset.mem_union.mp hn with hss | hr
            · exact False.elim (hi ((rows i).2.2.2.2.1 hss))
            · exact (residues i p).2.2.2.2.1 hr
          · exact False.elim (notfresh i ha hf)
        have hcont (i : ℕ) (ha : az.1 ≤ i) (hz : i < az.2)
            (hi : p ∉ A i) (hn : p ∉ A (i+1)) :
            rb (i+1) p = ra i p + (h (i+1) p - h i p) := by
          apply (residues i p).2.2.2.2.2.1
          apply Finset.mem_sdiff.mpr
          refine ⟨(supp i).2.2.1.mpr ⟨ha,hz,hi⟩, ?_⟩
          intro hr
          apply hn
          rw [(rows i).2.2.2.2.2.2.2.1]
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hr)
        have hend (hn : p ∉ A az.2) : rb az.2 p = 0 := by
          have hd := (supp az.2).2.2.2.2.mpr rfl
          rcases Finset.mem_union.mp hd with he | ha
          · exact (residues az.2 p).2.2.2.2.2.2 he
          · exact False.elim (hn (Finset.mem_sdiff.mp ha).1)
        have hr := reverse (fun i => p ∈ A i) az.1 az.2
          (fun i => h i p) (fun i => rb i p) (fun i => ra i p)
          haz hsingle hg hshare hstore hprom hcont hend
        refine ⟨haz,hzT,hsingle,supp,?_,hr.2.2.2,?_,?_⟩
        · intro i hi
          exact hr.1 i ((supp i).1 hi).1 ((supp i).1 hi).2 hi
        · intro i hm
          have hh := (supp i).2.1.mp hm
          exact hr.2.1 i hh.1 hh.2.1 hh.2.2
        · intro i hm
          have hh := (supp i).2.2.1.mp hm
          exact hr.2.2.1 i hh.1 hh.2.1 hh.2.2
  classical
  intro P _ _ V _ T A M F G E S K R U h rb ra hU hM hF rows tail residues
  obtain ⟨life,hlife⟩ :=
    existence V T A M F G E S K R U h rb ra hU hM hF rows tail residues
  refine ⟨life,hlife,?_⟩
  intro other hother
  funext p
  have hl := hlife p
  have ho := hother p
  cases he : life p with
  | none =>
    simp only [he] at hl ⊢
    cases hh : other p with
    | none => rfl
    | some bz =>
      simp only [hh] at ho
      have hb := (ho.2.2.2.1 bz.1).2.2.2.1.mpr rfl
      rcases Finset.mem_union.mp hb with hf | hg
      · exact False.elim ((hl bz.1).1 ((rows bz.1).1 hf))
      · exact False.elim ((hl bz.1).2.2 hg)
  | some az =>
    simp only [he] at hl ⊢
    cases hh : other p with
    | none =>
      simp only [hh] at ho
      have hb := (hl.2.2.2.1 az.1).2.2.2.1.mpr rfl
      rcases Finset.mem_union.mp hb with hf | hg
      · exact False.elim ((ho az.1).1 ((rows az.1).1 hf))
      · exact False.elim ((ho az.1).2.2 hg)
    | some bz =>
      simp only [hh] at ho
      have ha : bz.1 = az.1 :=
        (ho.2.2.2.1 az.1).2.2.2.1.mp ((hl.2.2.2.1 az.1).2.2.2.1.mpr rfl)
      have hz : bz.2 = az.2 :=
        (ho.2.2.2.1 az.2).2.2.2.2.mp ((hl.2.2.2.1 az.2).2.2.2.2.mpr rfl)
      exact congrArg some (Prod.ext ha hz)

end Green64MemoryFinal

end

/-! ## LiteralSourceRow -/

section

open scoped BigOperators
open Classical

namespace Green64Literal

variable {P : Type} [DecidableEq P]

noncomputable def pick (xs : List P) (s : Finset (Fin xs.length)) : List P :=
  s.toList.map xs.get

theorem pick_mem (xs : List P) (s : Finset (Fin xs.length)) (p : P) :
    p ∈ pick xs s ↔ ∃ j ∈ s, xs.get j = p := by
  simp [pick, List.mem_map]

theorem pick_toFinset (xs : List P) (s : Finset (Fin xs.length)) :
    (pick xs s).toFinset = s.image xs.get := by
  ext p
  simp [pick_mem, Finset.mem_image]

structure SourceRow (G : Type) [Fintype G] (slotCount : G → ℕ) where
  value : P → ℕ
  labelGroup : P → G
  activeSlots : (g : G) → Fin (slotCount g) → P
  nextSlots : (g : G) → Fin (slotCount g) → P
  sourcePerm : (g : G) → Equiv.Perm (Fin (slotCount g))
  targetPerm : (g : G) → Equiv.Perm (Fin (slotCount g))
  active : List P
  nextActive : List P
  sourceEndpoint : List P
  targetEndpoint : List P
  pendingBefore : List P
  pendingAfter : List P
  pendingNext : List P
  ghostBatch : List P
  ghostBatches : G → List P
  patternShared : (g : G) → Finset (Fin (slotCount g))
  freshTarget : List P
  termIndices : Finset (Fin pendingBefore.length)
  sharedIndices : Finset (Fin sourceEndpoint.length)
  storeIndices : Finset (Fin sourceEndpoint.length)
  promotionSlots : Finset (Fin targetEndpoint.length)
  promotionOld : promotionSlots ↪ Fin pendingAfter.length

  auxiliaryPrimes : List P
  smallSharedPrimes : List ℕ
  smallAuxiliaryPrimes : List ℕ
  everBornBefore : Finset P
  everBornAfter : Finset P
  freshBefore : List P
  residueBefore : (p : P) → ZMod (value p)
  residueAfter : (p : P) → ZMod (value p)
  residueNext : (p : P) → ZMod (value p)
  offsetBefore : ℤ
  offsetAfter : ℤ
  k : ℤ
  orientation : ℤ
  divisorD : ℕ
  theta : ℝ
  zeta : ℝ
  kernelK : ℂ
  rho : ℝ
  q : ℝ
  eta : ℝ
  groupV : G → ℝ
  baseline : P → ℝ
  auxiliaryMeasure : P → ℝ
  smallFactor : ℂ

variable {G : Type} [Fintype G] {slotCount : G → ℕ}

def ended (f : SourceRow (P := P) G slotCount) : Finset P :=
  f.termIndices.image f.pendingBefore.get

def shared (f : SourceRow (P := P) G slotCount) : Finset P :=
  f.sharedIndices.image f.sourceEndpoint.get

def stored (f : SourceRow (P := P) G slotCount) : Finset P :=
  f.storeIndices.image f.sourceEndpoint.get

def promoted (f : SourceRow (P := P) G slotCount) : Finset P :=
  f.promotionSlots.image f.targetEndpoint.get

structure RowValid (f : SourceRow (P := P) G slotCount) : Prop where
  numerical_prime : ∀ p, Nat.Prime (f.value p)
  numerical_injective : Function.Injective f.value
  source_order : f.sourceEndpoint =
    (Finset.univ : Finset (Σ g : G, Fin (slotCount g))).toList.map
      (fun a => f.activeSlots a.1 (f.sourcePerm a.1 a.2))
  target_order : f.targetEndpoint =
    (Finset.univ : Finset (Σ g : G, Fin (slotCount g))).toList.map
      (fun a => f.nextSlots a.1 (f.targetPerm a.1 a.2))
  source_groups : ∀ g j, f.labelGroup (f.activeSlots g j) = g
  target_groups : ∀ g j, f.labelGroup (f.nextSlots g j) = g
  ghost_group_order : f.ghostBatch =
    (Finset.univ.toList : List G).flatMap f.ghostBatches
  ghost_group_labels : ∀ g p, p ∈ f.ghostBatches g → f.labelGroup p = g
  shared_canonical_copy : ∀ g j, j ∈ f.patternShared g →
    f.activeSlots g j = f.nextSlots g j
  shared_source_pattern : ∀ g j,
    f.activeSlots g j ∈ shared f ↔ j ∈ f.patternShared g
  shared_target_pattern : ∀ g j,
    f.nextSlots g j ∈ shared f ↔ j ∈ f.patternShared g
  source_perm : f.sourceEndpoint.Perm f.active
  target_perm : f.targetEndpoint.Perm f.nextActive
  source_nodup : f.sourceEndpoint.Nodup
  target_nodup : f.targetEndpoint.Nodup
  active_nodup : f.active.Nodup
  pending_nodup : f.pendingBefore.Nodup
  pendingAfter_nodup : f.pendingAfter.Nodup
  pendingNext_nodup : f.pendingNext.Nodup
  ghost_nodup : f.ghostBatch.Nodup
  fresh_nodup : f.freshTarget.Nodup
  shared_store : Disjoint f.sharedIndices f.storeIndices
  term_zero : ∀ j ∈ f.termIndices,
    f.residueBefore (f.pendingBefore.get j) = 0
  ghost_operation : f.pendingAfter =
    f.pendingBefore.filter (fun p => p ∉ ended f) ++ f.ghostBatch
  promotion_matches : ∀ j : f.promotionSlots,
    f.targetEndpoint.get j.val = f.pendingAfter.get (f.promotionOld j)
  promotion_zero : ∀ j : f.promotionSlots,
    f.residueAfter (f.targetEndpoint.get j.val) +
      ((f.offsetAfter - f.offsetBefore : ℤ) : ZMod (f.value (f.targetEndpoint.get j.val))) = 0
  target_operation : f.nextActive.Perm
    (pick f.sourceEndpoint f.sharedIndices ++
     pick f.targetEndpoint f.promotionSlots ++ f.freshTarget)
  pending_operation : f.pendingNext =
    f.pendingAfter.filter (fun p => p ∉ promoted f) ++
    pick f.sourceEndpoint f.storeIndices

  fresh_before_active : f.freshBefore.toFinset ⊆ f.active.toFinset
  fresh_before_unused : Disjoint f.freshBefore.toFinset f.everBornBefore
  ghost_new : Disjoint f.ghostBatch.toFinset
    (f.everBornBefore ∪ f.freshBefore.toFinset)
  next_fresh_unused : Disjoint f.freshTarget.toFinset f.everBornAfter
  ever_update : f.everBornAfter =
    (f.everBornBefore ∪ f.freshBefore.toFinset) ∪ f.ghostBatch.toFinset
  auxiliary_ban : ∀ p ∈ f.auxiliaryPrimes,
    p ∉ f.active ∧ p ∉ f.nextActive
  nondividing_store : ∀ p ∈ stored f, ¬ f.value p ∣ f.divisorD
  nondividing_promotion : ∀ p ∈ promoted f, ¬ f.value p ∣ f.divisorD
  signed_orientation : f.orientation = 1 ∨ f.orientation = -1
  divisor_from_groups : f.divisorD =
    (f.smallSharedPrimes.prod * f.smallAuxiliaryPrimes.prod) *
    ((pick f.sourceEndpoint f.sharedIndices).map f.value).prod *
    (f.auxiliaryPrimes.map f.value).prod
  offset_update :
    f.offsetAfter = f.offsetBefore + f.orientation * f.k * f.divisorD
  ghost_birth_zero : ∀ p ∈ f.ghostBatch, f.residueAfter p = 0
  old_pending_unchanged : ∀ p ∈ f.pendingBefore, p ∉ ended f →
    f.residueAfter p = f.residueBefore p
  store_reset : ∀ p ∈ stored f, f.residueNext p =
    ((f.offsetAfter - f.offsetBefore : ℤ) : ZMod (f.value p))
  surviving_translation : ∀ p ∈ f.pendingAfter.toFinset \ promoted f,
    f.residueNext p = f.residueAfter p +
      ((f.offsetAfter - f.offsetBefore : ℤ) : ZMod (f.value p))
  shared_congruence : ∀ p ∈ shared f,
    (f.offsetBefore : ZMod (f.value p)) =
      (f.offsetAfter : ZMod (f.value p))

theorem ended_subset (f : SourceRow (P := P) G slotCount) :
    ended f ⊆ f.pendingBefore.toFinset := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
  exact List.mem_toFinset.mpr (List.get_mem _ _)

theorem row_ghost_support (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) :
    f.pendingAfter.toFinset =
      (f.pendingBefore.toFinset \ ended f) ∪ f.ghostBatch.toFinset := by
  ext p
  simp [h.ghost_operation, Finset.mem_union, Finset.mem_sdiff]

theorem row_target_support (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) :
    f.nextActive.toFinset =
      (shared f ∪ promoted f) ∪ f.freshTarget.toFinset := by
  ext p
  simp only [List.mem_toFinset, Finset.mem_union]
  rw [h.target_operation.mem_iff]
  simp [pick_mem, shared, promoted, Finset.mem_image, or_assoc]

theorem row_pending_support (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) :
    f.pendingNext.toFinset =
      (((f.pendingBefore.toFinset \ ended f) ∪ f.ghostBatch.toFinset) \
      promoted f) ∪ stored f := by
  ext p
  rw [h.pending_operation]
  simp [row_ghost_support f h, pick_toFinset, stored,
    Finset.mem_union, Finset.mem_sdiff]


end Green64Literal

end

/-! ## PhysicalActualLiteralHistoryActiveNormalize -/

section

open Classical

namespace Green64Literal

/-- Preserve all physical fields, including OLD indices and the independent
source/target frames, while using raw endpoints as active-list order. -/
noncomputable def endpointActiveRow
    {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}
    (f : SourceRow (P := P) G slots) :
    SourceRow (P := P) G slots :=
  { f with active := f.sourceEndpoint, nextActive := f.targetEndpoint }

theorem row_valid_endpoint_active
    {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}
    (f : SourceRow (P := P) G slots) (h : RowValid f) :
    RowValid (endpointActiveRow f) := by
  classical
  have hFresh : f.freshBefore.toFinset ⊆ f.sourceEndpoint.toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr
      ((h.source_perm.mem_iff).mpr
        (List.mem_toFinset.mp (h.fresh_before_active hp)))
  have hAux : ∀ p ∈ f.auxiliaryPrimes,
      p ∉ f.sourceEndpoint ∧ p ∉ f.targetEndpoint := by
    intro p hp
    obtain ⟨h1, h2⟩ := h.auxiliary_ban p hp
    exact ⟨fun x => h1 ((h.source_perm.mem_iff).mp x),
      fun x => h2 ((h.target_perm.mem_iff).mp x)⟩
  refine {
    numerical_prime := h.numerical_prime
    numerical_injective := h.numerical_injective
    source_order := h.source_order
    target_order := h.target_order
    source_groups := h.source_groups
    target_groups := h.target_groups
    ghost_group_order := h.ghost_group_order
    ghost_group_labels := h.ghost_group_labels
    shared_canonical_copy := h.shared_canonical_copy
    shared_source_pattern := h.shared_source_pattern
    shared_target_pattern := h.shared_target_pattern
    source_perm := List.Perm.refl _
    target_perm := List.Perm.refl _
    source_nodup := h.source_nodup
    target_nodup := h.target_nodup
    active_nodup := h.source_nodup
    pending_nodup := h.pending_nodup
    pendingAfter_nodup := h.pendingAfter_nodup
    pendingNext_nodup := h.pendingNext_nodup
    ghost_nodup := h.ghost_nodup
    fresh_nodup := h.fresh_nodup
    shared_store := h.shared_store
    term_zero := h.term_zero
    ghost_operation := h.ghost_operation
    promotion_matches := h.promotion_matches
    promotion_zero := h.promotion_zero
    target_operation := h.target_perm.trans h.target_operation
    pending_operation := h.pending_operation
    fresh_before_active := hFresh
    fresh_before_unused := h.fresh_before_unused
    ghost_new := h.ghost_new
    next_fresh_unused := h.next_fresh_unused
    ever_update := h.ever_update
    auxiliary_ban := hAux
    nondividing_store := h.nondividing_store
    nondividing_promotion := h.nondividing_promotion
    signed_orientation := h.signed_orientation
    divisor_from_groups := h.divisor_from_groups
    offset_update := h.offset_update
    ghost_birth_zero := h.ghost_birth_zero
    old_pending_unchanged := h.old_pending_unchanged
    store_reset := h.store_reset
    surviving_translation := h.surviving_translation
    shared_congruence := h.shared_congruence
  }

end Green64Literal

end

/-! ## PhysicalActualLiteralHistoryFreshRebase -/

section

open Classical

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Present an already-proved first-birth set in another list order.
The data of the physical transition and the exact OLD indices are untouched. -/
noncomputable def freshBeforeRebase
    (f : SourceRow (P := P) G slots) (xs : List P) :
    SourceRow (P := P) G slots :=
  { f with freshBefore := xs }

theorem row_valid_fresh_before_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hx : xs.toFinset = f.freshBefore.toFinset) :
    RowValid (freshBeforeRebase f xs) := by
  have hFreshActive : xs.toFinset ⊆ f.active.toFinset := by
    rw [hx]; exact h.fresh_before_active
  have hFreshUnused : Disjoint xs.toFinset f.everBornBefore := by
    rw [hx]; exact h.fresh_before_unused
  have hGhostNew :
      Disjoint f.ghostBatch.toFinset
        (f.everBornBefore ∪ xs.toFinset) := by
    rw [hx]; exact h.ghost_new
  have hEver :
      f.everBornAfter =
        (f.everBornBefore ∪ xs.toFinset) ∪ f.ghostBatch.toFinset := by
    rw [hx]; exact h.ever_update
  refine {

    numerical_prime := h.numerical_prime
    numerical_injective := h.numerical_injective
    source_order := h.source_order
    target_order := h.target_order
    source_groups := h.source_groups
    target_groups := h.target_groups
    ghost_group_order := h.ghost_group_order
    ghost_group_labels := h.ghost_group_labels
    shared_canonical_copy := h.shared_canonical_copy
    shared_source_pattern := h.shared_source_pattern
    shared_target_pattern := h.shared_target_pattern
    source_perm := h.source_perm
    target_perm := h.target_perm
    source_nodup := h.source_nodup
    target_nodup := h.target_nodup
    active_nodup := h.active_nodup
    pending_nodup := h.pending_nodup
    pendingAfter_nodup := h.pendingAfter_nodup
    pendingNext_nodup := h.pendingNext_nodup
    ghost_nodup := h.ghost_nodup
    fresh_nodup := h.fresh_nodup
    shared_store := h.shared_store
    term_zero := h.term_zero
    ghost_operation := h.ghost_operation
    promotion_matches := h.promotion_matches
    promotion_zero := h.promotion_zero
    target_operation := h.target_operation

    pending_operation := h.pending_operation
    fresh_before_active := hFreshActive
    fresh_before_unused := hFreshUnused
    ghost_new := hGhostNew
    next_fresh_unused := h.next_fresh_unused
    ever_update := hEver
    auxiliary_ban := h.auxiliary_ban
    nondividing_store := h.nondividing_store
    nondividing_promotion := h.nondividing_promotion
    signed_orientation := h.signed_orientation
    divisor_from_groups := h.divisor_from_groups
    offset_update := h.offset_update
    ghost_birth_zero := h.ghost_birth_zero
    old_pending_unchanged := h.old_pending_unchanged
    store_reset := h.store_reset
    surviving_translation := h.surviving_translation
    shared_congruence := h.shared_congruence
  }

end Green64Literal

end

/-! ## LiteralRowConservation -/

section

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slotCount : G → ℕ}

theorem shared_subset_active (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) : shared f ⊆ f.active.toFinset := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j, _, hj⟩
  have hs : p ∈ f.sourceEndpoint := by
    rw [← hj]
    exact List.get_mem _ _
  exact List.mem_toFinset.mpr (h.source_perm.mem_iff.mp hs)

theorem stored_subset_active (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) : stored f ⊆ f.active.toFinset := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j, _, hj⟩
  have hs : p ∈ f.sourceEndpoint := by
    rw [← hj]
    exact List.get_mem _ _
  exact List.mem_toFinset.mpr (h.source_perm.mem_iff.mp hs)

theorem stored_disjoint_shared (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) : Disjoint (stored f) (shared f) := by
  apply Finset.disjoint_left.mpr
  intro p hp hs
  rcases Finset.mem_image.mp hp with ⟨j,hj,hjp⟩
  rcases Finset.mem_image.mp hs with ⟨k,hk,hkp⟩
  have inj := List.nodup_iff_injective_get.mp h.source_nodup
  have jk : j = k := inj (hjp.trans hkp.symm)
  have jShared : j ∈ f.sharedIndices := by simpa [jk] using hk
  exact Finset.disjoint_left.mp h.shared_store jShared hj

theorem promoted_subset_after (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) : promoted f ⊆ f.pendingAfter.toFinset := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j,hj,hjp⟩
  have hm := List.get_mem f.pendingAfter (f.promotionOld ⟨j,hj⟩)
  have eq := h.promotion_matches ⟨j,hj⟩
  have hp' : p ∈ f.pendingAfter := by
    rw [← hjp, eq]
    exact hm
  exact List.mem_toFinset.mpr hp'

theorem row_source_constraints (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) :
    ended f ⊆ f.pendingBefore.toFinset ∧
    shared f ⊆ f.active.toFinset ∧
    stored f ⊆ f.active.toFinset \ shared f ∧
    promoted f ⊆ f.pendingAfter.toFinset ∧
    f.freshTarget.toFinset ⊆ f.nextActive.toFinset := by
  refine ⟨ended_subset f, shared_subset_active f h, ?_,
    promoted_subset_after f h, ?_⟩
  · intro p hp
    exact Finset.mem_sdiff.mpr ⟨stored_subset_active f h hp,
      fun hs => (Finset.disjoint_left.mp (stored_disjoint_shared f h)) hp hs⟩
  · intro p hp
    rw [row_target_support f h]
    exact Finset.mem_union_right _ hp

end Green64Literal

end

/-! ## SourceRoughSemantic -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Exact finite alphabet equivalence, including p=2 and boundary p=z. -/
theorem prime_le_cutoff_iff (z : ℝ) (hz : 0 ≤ z) (p : ℕ) :
    p ∈ (Finset.range (Nat.floor z + 1)).filter Nat.Prime ↔
      Nat.Prime p ∧ (p : ℝ) ≤ z := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp,hpr⟩
    have hp' : p ≤ Nat.floor z := by omega
    exact ⟨hpr,(show (p:ℝ) ≤ (Nat.floor z:ℝ) by exact_mod_cast hp').trans (Nat.floor_le hz)⟩
  · rintro ⟨hpr,hpz⟩
    have hfloor : p ≤ Nat.floor z := Nat.le_floor hpz
    exact ⟨by omega,hpr⟩

/-- Source count uses the original finite prime alphabet. -/
noncomputable def sourceRoughFiltered (z x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 (Nat.floor x)).filter
    (fun n => ∀ p ∈ ((Finset.range (Nat.floor z + 1)).filter Nat.Prime), ¬ p ∣ n)

/-- The quantification over every natural prime <=z is EXACTLY
 the source finite-alphabet roughness predicate, no squarefree shortcut. -/
theorem roughSet_eq_source_filtered (z x : ℝ) (hz : 0 ≤ z) :
    roughSet z x = sourceRoughFiltered z x := by
  classical
  ext n
  simp only [roughSet, sourceRoughFiltered, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hn,h⟩
    refine ⟨hn,?_⟩
    intro p hp
    have he := (prime_le_cutoff_iff z hz p).mp (Finset.mem_filter.mpr hp)
    exact h p he.1 he.2
  · rintro ⟨hn,h⟩
    refine ⟨hn,?_⟩
    intro p hp hpz
    exact h p (Finset.mem_filter.mp ((prime_le_cutoff_iff z hz p).mpr ⟨hp,hpz⟩))

end Green64Analytic.OrderedPrimeRough

end

/-! ## SourcePrimeTupleCount -/

section

set_option maxHeartbeats 900000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Exact REPLAY of the original small-b sieve's natural-count meaning.
The prime threshold is x^b; no change of sieve, no squarefree
restriction, and n=1 is included. -/
theorem roughSet_card_eq_source_roughCount (b x : ℝ)
    (hb : 0 < b) (hx : 1 < x) :
    ((roughSet (x^b) x).card : ℝ) =
        Green64Analytic.SmallB.roughCount b x := by
  have _ := hb
  have hz : 0 ≤ x^b := Real.rpow_nonneg (by linarith : 0 ≤ x) _
  rw [roughSet_eq_source_filtered (x^b) x hz]
  rw [Green64Analytic.SmallB.roughCount_is_actual]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext n
  simp [sourceRoughFiltered, Green64Analytic.SmallB.roughAlphabet]


/-- Exact source-normalized factorial inequality, now using the
predecessor's ACTUAL roughCount b x, not an abstract rough set.
This is the finite combinatorial half of the ordered-prime lower
comparison. All repeated factors and ell=0 survive. -/
theorem source_ordered_prime_factorial_bound
    (ell : ℕ) (b x : ℝ) (hb : 0 < b) (hx : 1 < x) :
    ((allPrimeTuples ell (x^b) x).card : ℝ) /
      (ell.factorial : ℝ) ≤
      Green64Analytic.SmallB.roughCount b x := by
  have hnat := allPrimeTuples_card_le_rough ell (x^b) x (by linarith)
  have hcast :
      ((allPrimeTuples ell (x^b) x).card : ℝ) ≤
        (ell.factorial : ℝ) * ((roughSet (x^b) x).card : ℝ) := by
    exact_mod_cast hnat
  rw [roughSet_card_eq_source_roughCount b x hb hx] at hcast
  have hf : (0:ℝ) < (ell.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos ell
  apply (div_le_iff₀ hf).mpr
  simpa only [mul_comm] using hcast

end Green64Analytic.OrderedPrimeRough

end

/-! ## LastPrimeExtensions -/

section

set_option maxHeartbeats 1100000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Actual finite collection of last-prime extensions for a fixed
ordered prefix. In contrast to an abstract product measure, the
last coordinate is the literal natural prime p. -/
noncomputable def lastPrimeExtensions
    (pre : List ℕ) (z y : ℝ) : Finset (List ℕ) :=
  (primeWindow z y).image (fun p => pre ++ [p])

theorem lastPrimeExtensions_card (pre : List ℕ) (z y : ℝ) :
    (lastPrimeExtensions pre z y).card =
      (primeWindow z y).card := by
  classical
  unfold lastPrimeExtensions
  apply (Finset.card_image_iff).mpr
  intro p hp q hq h
  have htail := List.append_inj_right h (rfl : pre.length = pre.length)
  simpa using htail

/-- Different prefixes of the same length have disjoint
last-prime extensions. This excludes all hidden multiplicity
in the last-coordinate decomposition, including repeated primes. -/
theorem lastPrimeExtensions_disjoint
    (pre₁ pre₂ : List ℕ) (z y₁ y₂ : ℝ)
    (hlen : pre₁.length = pre₂.length) (hne : pre₁ ≠ pre₂) :
    Disjoint (lastPrimeExtensions pre₁ z y₁)
      (lastPrimeExtensions pre₂ z y₂) := by
  classical
  apply Finset.disjoint_left.mpr
  intro l h₁ h₂
  rcases Finset.mem_image.mp h₁ with ⟨p,hp,rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨q,hq,heq⟩
  have hEq : pre₁ = pre₂ :=
    List.append_inj_left heq.symm hlen
  exact hne hEq

/-- Each actual prime-window last-coordinate extension
belongs to the full source ordered-tuple family; no
distinct-prime or squarefree restriction on the prefix. -/
theorem lastPrimeExtensions_subset
    (ell : ℕ) (pre : List ℕ) (z x : ℝ)
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hpre : pre ∈ allPrimeTuples ell z x) :
    lastPrimeExtensions pre z (x/(pre.prod:ℝ)) ⊆
      allPrimeTuples (ell+1) z x := by
  classical
  have hpreinfo := (mem_allPrimeTuples_iff ell z x hx pre).mp hpre
  have hposReal : (0:ℝ) < (pre.prod:ℝ) := by
    exact_mod_cast hpreinfo.2.2.1
  have hy : 0 ≤ x/(pre.prod:ℝ) := div_nonneg hx hposReal.le
  intro l hl
  rcases Finset.mem_image.mp hl with ⟨p,hp,rfl⟩
  have hpinfo :=
    (mem_primeWindow_iff_nonneg z (x/(pre.prod:ℝ)) hz hy p).mp hp
  apply (mem_allPrimeTuples_iff (ell+1) z x hx (pre++[p])).mpr
  refine ⟨by simp [hpreinfo.1],?_,?_,?_⟩
  · intro q hq
    have hq' : q ∈ pre ∨ q = p := by
      simpa only [List.mem_append, List.mem_singleton] using hq
    rcases hq' with hq | hq
    · exact hpreinfo.2.1 q hq
    · subst q
      exact ⟨hpinfo.1,hpinfo.2.1⟩
  · simp only [List.prod_append, List.prod_singleton]
    exact Nat.mul_pos hpreinfo.2.2.1 hpinfo.1.pos
  · have hpos : (0:ℝ) < (pre.prod:ℝ) := by
      exact_mod_cast hpreinfo.2.2.1
    have hbound : (p:ℝ)*(pre.prod:ℝ) ≤ x :=
      (le_div_iff₀ hpos).mp hpinfo.2.2
    simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
    nlinarith


/-- Every ordered source tuple of length ell+1 is obtained uniquely
by appending one genuine last prime to an ordered ell-prefix. -/
theorem allPrimeTuples_succ_eq_extensions
    (ell : ℕ) (z x : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    allPrimeTuples (ell+1) z x =
      (allPrimeTuples ell z x).biUnion
        (fun pre => lastPrimeExtensions pre z (x/(pre.prod:ℝ))) := by
  classical
  ext l
  constructor
  · intro hl
    have hinfo := (mem_allPrimeTuples_iff (ell+1) z x hx l).mp hl
    have hne : l ≠ [] := by
      intro he
      have hlen := hinfo.1
      simp only [he, List.length_nil] at hlen
      omega
    let pre : List ℕ := l.dropLast
    let p : ℕ := l.getLast hne
    have hdecomp : pre ++ [p] = l :=
      List.dropLast_append_getLast hne
    have hplen : pre.length = ell := by
      have hlen := congrArg List.length hdecomp
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hprepr : ∀ q ∈ pre, Nat.Prime q ∧ z < (q:ℝ) := by
      intro q hq
      apply hinfo.2.1
      rw [← hdecomp]
      exact List.mem_append_left _ hq
    have hpinfo : Nat.Prime p ∧ z < (p:ℝ) := by
      apply hinfo.2.1
      rw [← hdecomp]
      exact List.mem_append_right _ (by simp)
    have hprepos : 0 < pre.prod :=
      List.prod_pos (fun q hq => (hprepr q hq).1.pos)
    have hprodEq : l.prod = pre.prod*p := by
      rw [← hdecomp]
      simp only [List.prod_append, List.prod_singleton]
    have hprebound : (pre.prod:ℝ) ≤ x := by
      have hmul : (1:ℝ) ≤ p := by
        exact_mod_cast hpinfo.1.one_le
      have hpcast : (l.prod:ℝ) = (pre.prod:ℝ)*(p:ℝ) := by
        exact_mod_cast hprodEq
      have hpre_nonneg : (0:ℝ) ≤ (pre.prod:ℝ) := by
        exact_mod_cast hprepos.le
      nlinarith [mul_nonneg hpre_nonneg (sub_nonneg.mpr hmul),
        hinfo.2.2.2]
    have hpre : pre ∈ allPrimeTuples ell z x := by
      apply (mem_allPrimeTuples_iff ell z x hx pre).mpr
      exact ⟨hplen,hprepr,hprepos,hprebound⟩
    have hpreposR : (0:ℝ) < (pre.prod:ℝ) := by
      exact_mod_cast hprepos
    have hlastbound : (p:ℝ) ≤ x/(pre.prod:ℝ) := by
      apply (le_div_iff₀ hpreposR).mpr
      have hpcast : (l.prod:ℝ) = (pre.prod:ℝ)*(p:ℝ) := by
        exact_mod_cast hprodEq
      nlinarith [hinfo.2.2.2]
    have hylower : 0 ≤ x/(pre.prod:ℝ) := div_nonneg hx hpreposR.le
    have hlast :
        p ∈ primeWindow z (x/(pre.prod:ℝ)) :=
      (mem_primeWindow_iff_nonneg z (x/(pre.prod:ℝ)) hz hylower p).mpr
        ⟨hpinfo.1,hpinfo.2,hlastbound⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨pre,hpre,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p,hlast,hdecomp⟩
  · intro hl
    rcases Finset.mem_biUnion.mp hl with ⟨pre,hpre,hext⟩
    exact lastPrimeExtensions_subset ell pre z x hx hz hpre hext

/-- Exact finite Fubini decomposition of the real source ordered
prime count into its last prime and all ordered prefixes.
This is the missing combinatorial interface for applying the PNT
estimate on the last prime and then compact-grid reciprocal measures. -/
theorem allPrimeTuples_succ_card_sum
    (ell : ℕ) (z x : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    (allPrimeTuples (ell+1) z x).card =
      ∑ pre ∈ allPrimeTuples ell z x,
         (primeWindow z (x/(pre.prod:ℝ))).card := by
  classical
  have hdisj :
      ((allPrimeTuples ell z x : Finset (List ℕ)) : Set (List ℕ)).PairwiseDisjoint
      (fun pre => lastPrimeExtensions pre z (x/(pre.prod:ℝ))) := by
    intro pre hp q hq hne
    have hlpre := ((mem_allPrimeTuples_iff ell z x hx pre).mp hp).1
    have hlq := ((mem_allPrimeTuples_iff ell z x hx q).mp hq).1
    exact lastPrimeExtensions_disjoint pre q z (x/(pre.prod:ℝ))
      (x/(q.prod:ℝ)) (hlpre.trans hlq.symm) hne
  rw [allPrimeTuples_succ_eq_extensions ell z x hx hz,
    Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro pre hp
  exact lastPrimeExtensions_card pre z (x/(pre.prod:ℝ))

/-- Source-exact last-prime PNT lower bound for ANY chosen
finite set of legal ordered prefixes satisfying the explicit
uniform PNT threshold and last-coordinate gap.

No compact-grid convergence, simplex limit, or positive prime-mass
premise is assumed. Every discarded prefix contributes a nonnegative
count, and the prime interval is the ACTUAL natural-prime interval. -/
theorem ordered_tuples_lower_from_PNT2
    (ell : ℕ) (z x Y C : ℝ) (G : Finset (List ℕ))
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hG : G ⊆ allPrimeTuples ell z x)
    (hroom : ∀ pre ∈ G, z ≤ x/(pre.prod:ℝ) ∧
      Y ≤ x/(pre.prod:ℝ))
    (hPNT2 : ∀ u : ℝ, Y ≤ u →
      |(Nat.primeCounting (Nat.floor u):ℝ) - u/Real.log u| ≤
        C*u/(Real.log u)^2) :
    (∑ pre ∈ G,
      ((x/(pre.prod:ℝ))/Real.log (x/(pre.prod:ℝ)) -
        C*(x/(pre.prod:ℝ)) /
          (Real.log (x/(pre.prod:ℝ)))^2 - (z+1))) ≤
        ((allPrimeTuples (ell+1) z x).card : ℝ) := by
  classical
  have hcast :
      ((allPrimeTuples (ell+1) z x).card : ℝ) =
      ∑ pre ∈ allPrimeTuples ell z x,
        ((primeWindow z (x/(pre.prod:ℝ))).card:ℝ) := by
    exact_mod_cast allPrimeTuples_succ_card_sum ell z x hx hz
  have hsmall : (∑ pre ∈ G,
      ((x/(pre.prod:ℝ))/Real.log (x/(pre.prod:ℝ)) -
        C*(x/(pre.prod:ℝ)) /
          (Real.log (x/(pre.prod:ℝ)))^2 - (z+1))) ≤
      ∑ pre ∈ G, ((primeWindow z (x/(pre.prod:ℝ))).card:ℝ) := by
    apply Finset.sum_le_sum
    intro pre hpre
    exact primeWindow_from_PNT2 Y C z (x/(pre.prod:ℝ))
      hz (hroom pre hpre).1 (hroom pre hpre).2 hPNT2
  have hlarge :
      (∑ pre ∈ G, ((primeWindow z (x/(pre.prod:ℝ))).card:ℝ)) ≤
      ∑ pre ∈ allPrimeTuples ell z x,
        ((primeWindow z (x/(pre.prod:ℝ))).card:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hG
    intro pre hp hnot
    positivity
  exact (hsmall.trans hlarge).trans_eq hcast.symm

end Green64Analytic.OrderedPrimeRough

end

/-! ## SourceSWModernSmoothExistence -/

section

open MeasureTheory Set Real
open scoped ContDiff

/-! Source-compatible auxiliary from the pre-existing PrimeNumberTheoremAnd
Erdos970.SmoothExistence proof. This ONLY restores a theorem omitted from
the Lean4.34 ported SmoothExistence module; it adds no new axiom. -/
lemma sourceSWModernSmoothExistence434 :∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport]
      have hSupportId : Function.support (fun x : ℝ => x) = {0}ᶜ := by
        ext x
        simp [Function.mem_support]
      rw [hSupportId]
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end

