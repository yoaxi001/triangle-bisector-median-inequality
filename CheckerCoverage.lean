import Certificate
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace LiuCertificate

def InBox (box : Box) (a b : ℝ) : Prop :=
  (box.al:ℝ) ≤ a ∧ a ≤ (box.ah:ℝ) ∧ (box.bl:ℝ) ≤ b ∧ b ≤ (box.bh:ℝ)

def Domain (a b : ℝ) : Prop := (s:ℝ) ≤ a+b ∧ a ≤ b ∧ b ≤ (s:ℝ)

theorem empty_sound (box : Box) (a b : ℝ)
    (he : emptyCheck box = true) (hi : InBox box a b) (hd : Domain a b) : False := by
  have he' : box.ah+box.bh < s ∨ box.al > box.bh := by
    simpa only [emptyCheck, Bool.or_eq_true, decide_eq_true_eq] using he
  obtain ⟨ha0,ha1,hb0,hb1⟩ := hi
  obtain ⟨hs,hab,hbs⟩ := hd
  rcases he' with he' | he'
  · have hh : (box.ah:ℝ)+(box.bh:ℝ) < s := by exact_mod_cast he'
    linarith
  · have hh : (box.bh:ℝ) < box.al := by exact_mod_cast he'
    linarith

-- Soundness of subdivision is unconditional; leaf correctness is explicit.
-- This theorem alone does not supply proofs of the two leaf hypotheses.
theorem check_sound (P : ℝ → ℝ → Prop)
    (local_sound : ∀ box a b, localCheck box = true → InBox box a b → Domain a b → P a b)
    (interval_sound : ∀ box ma mb mc wa wb wc a b,
      intervalCheck box ma mb mc wa wb wc = true → InBox box a b → Domain a b → P a b)
    (cert : Cert) :
    ∀ box a b, check box cert = true → InBox box a b → Domain a b → P a b := by
  induction cert with
  | empty =>
    intro box a b hcheck hi hd
    exact False.elim (empty_sound box a b hcheck hi hd)
  | localPatch =>
    intro box a b hcheck hi hd
    exact local_sound box a b hcheck hi hd
  | interval ma mb mc wa wb wc =>
    intro box a b hcheck hi hd
    exact interval_sound box ma mb mc wa wb wc a b hcheck hi hd
  | split left right ihl ihr =>
    intro box a b hcheck hi hd
    obtain ⟨ha0,ha1,hb0,hb1⟩ := hi
    simp only [check] at hcheck
    split at hcheck
    · simp only [Bool.and_eq_true] at hcheck
      obtain ⟨hl,hr⟩ := hcheck
      by_cases hm : a ≤ (((box.al+box.ah)/2:ℕ):ℝ)
      · exact ihl {box with ah := (box.al+box.ah)/2} a b hl ⟨ha0,hm,hb0,hb1⟩ hd
      · exact ihr {box with al := (box.al+box.ah)/2} a b hr ⟨le_of_lt (lt_of_not_ge hm),ha1,hb0,hb1⟩ hd
    · simp only [Bool.and_eq_true] at hcheck
      obtain ⟨hl,hr⟩ := hcheck
      by_cases hm : b ≤ (((box.bl+box.bh)/2:ℕ):ℝ)
      · exact ihl {box with bh := (box.bl+box.bh)/2} a b hl ⟨ha0,ha1,hb0,hm⟩ hd
      · exact ihr {box with bl := (box.bl+box.bh)/2} a b hr ⟨ha0,ha1,le_of_lt (lt_of_not_ge hm),hb1⟩ hd

theorem verified_cover (P : ℝ → ℝ → Prop)
    (local_sound : ∀ box a b, localCheck box = true → InBox box a b → Domain a b → P a b)
    (interval_sound : ∀ box ma mb mc wa wb wc a b,
      intervalCheck box ma mb mc wa wb wc = true → InBox box a b → Domain a b → P a b)
    (a b : ℝ) (hi : InBox root a b) (hd : Domain a b) : P a b :=
  check_sound P local_sound interval_sound certificate root a b certificate_passes hi hd

#print axioms verified_cover
#print axioms empty_sound
#print axioms check_sound
end LiuCertificate
