import Main

namespace LiuEquality
open LiuReal LiuMain LiuCertificate

noncomputable def defect (a b c : ℝ) : ℝ :=
  (bisector a b c+bisector b c a+bisector c a b)*
    ((median a b c)^3+(median b c a)^3+(median c a b)^3)-((a+b+c)/2)^4

theorem defect_scale (t a b c : ℝ) (ht : 0<t)
    (hab : a+b≠0) (hbc : b+c≠0) (hca : c+a≠0) :
    defect (t*a) (t*b) (t*c)=t^4*defect a b c := by
  unfold defect
  rw [median_scale t a b c ht,median_scale t b c a ht,median_scale t c a b ht,
    bisector_scale t a b c ht hbc,bisector_scale t b c a ht hca,bisector_scale t c a b ht hab]
  ring

theorem local_equality (p q r : ℝ) (hs : p+q+r=0)
    (hp : |p|≤1/10) (hq : |q|≤1/10) (hr : |r|≤1/10)
    (he : defect (1+p) (1+q) (1+r)=0) : p=0 ∧ q=0 ∧ r=0 := by
  have gap := local_triangle_gap p q r hs hp hq hr
  have hsum : ((1+p)+(1+q)+(1+r))/2=(3/2:ℝ) := by linarith
  unfold defect at he
  rw [hsum] at he
  norm_num only [show (3/2:ℝ)^4=81/16 by norm_num] at he
  have hT : p^2+q^2+r^2≤0 := by nlinarith only [gap,he]
  exact ⟨by nlinarith only [hT,sq_nonneg q,sq_nonneg r],
    by nlinarith only [hT,sq_nonneg p,sq_nonneg r],
    by nlinarith only [hT,sq_nonneg p,sq_nonneg q]⟩

theorem mean_equality (a b c : ℝ) (ht : 0<(a+b+c)/3)
    (he : defect a b c=0)
    (hp : |a/((a+b+c)/3)-1|≤1/10)
    (hq : |b/((a+b+c)/3)-1|≤1/10)
    (hr : |c/((a+b+c)/3)-1|≤1/10) : a=b ∧ b=c := by
  let t := (a+b+c)/3
  let p := a/t-1
  let q := b/t-1
  let r := c/t-1
  have ht0 : t≠0 := ne_of_gt ht
  have htSum : a+b+c=3*t := by dsimp [t]; ring
  have hs : p+q+r=0 := by
    dsimp only [p,q,r]
    field_simp [ht0]
    <;> nlinarith only [htSum]
  have pp := positive_one_add p hp
  have pq := positive_one_add q hq
  have pr := positive_one_add r hr
  have ha : t*(1+p)=a := by dsimp only [p]; field_simp [ht0]
  have hb : t*(1+q)=b := by dsimp only [q]; field_simp [ht0]
  have hc : t*(1+r)=c := by dsimp only [r]; field_simp [ht0]
  have hscale := defect_scale t (1+p) (1+q) (1+r) ht
    (ne_of_gt (add_pos pp pq)) (ne_of_gt (add_pos pq pr)) (ne_of_gt (add_pos pr pp))
  rw [ha,hb,hc,he] at hscale
  have hn : defect (1+p) (1+q) (1+r)=0 := by
    have hz : t^4*defect (1+p) (1+q) (1+r)=0 := hscale.symm
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 ht0)
  obtain ⟨hp0,hq0,hr0⟩ := local_equality p q r hs hp hq hr hn
  rw [hp0] at ha
  rw [hq0] at hb
  rw [hr0] at hc
  constructor <;> nlinarith only [ha,hb,hc]

theorem interval_leaf_strict (box : Box) (ma mb mc wa wb wc : ℕ) (a b : ℝ)
    (hcheck : intervalCheck box ma mb mc wa wb wc = true)
    (hi : InBox box a b) (hd : Domain a b) : 0<defect a b s := by
  have hchecks :
      (4*s^2*ma^2 ≤ q^2*(2*box.bl^2+2*s^2-box.ah^2)) ∧
      (s^2*(box.bh+s)^2*wa^2 ≤ q^2*box.bl*s*(box.al+box.bl+s)*(box.bl+s-box.ah)) ∧
      (4*s^2*mb^2 ≤ q^2*(2*s^2+2*box.al^2-box.bh^2)) ∧
      (s^2*(s+box.ah)^2*wb^2 ≤ q^2*s*box.al*(box.bl+s+box.al)*(s+box.al-box.bh)) ∧
      (4*s^2*mc^2 ≤ q^2*(2*box.al^2+2*box.bl^2-s^2)) ∧
      (s^2*(box.ah+box.bh)^2*wc^2 ≤ q^2*box.al*box.bl*(s+box.al+box.bl)*(box.al+box.bl-s)) ∧
      (q^4*(box.ah+box.bh+s)^4 < 16*s^4*(wa+wb+wc)*(ma^3+mb^3+mc^3)) := by
    simpa only [intervalCheck,radicalCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hcheck
  obtain ⟨hma,hwa,hmb,hwb,hmc,hwc,hprod⟩ := hchecks
  obtain ⟨ha,ha1,hb,hb1⟩ := hi
  obtain ⟨htri,hab,hbS⟩ := hd
  have hs := certified_triangle_interval a b s q box.al box.ah box.bl box.bh ma mb mc wa wb wc
    (by decide) (by decide) ha ha1 hb hb1 hab hbS htri hma hmb hmc hwa hwb hwc hprod
  unfold defect
  linarith only [hs]

theorem local_leaf_equality (box : Box) (a b : ℝ)
    (hcheck : localCheck box = true) (hi : InBox box a b) (hd : Domain a b) : defect a b s=0 → a=b ∧ b=(s:ℝ) := by
  intro he
  have checks :
      (10*absDiff (2*box.al) (box.bh+s) ≤ box.al+box.bl+s) ∧
      (10*absDiff (2*box.ah) (box.bl+s) ≤ box.al+box.bl+s) ∧
      (10*absDiff (2*box.bl) (box.ah+s) ≤ box.al+box.bl+s) ∧
      (10*absDiff (2*box.bh) (box.al+s) ≤ box.al+box.bl+s) ∧
      (10*absDiff (2*s) (box.ah+box.bh) ≤ box.al+box.bl+s) ∧
      (10*absDiff (2*s) (box.al+box.bl) ≤ box.al+box.bl+s) := by
    simpa only [localCheck,List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true] using hcheck
  obtain ⟨c1,c2,c3,c4,c5,c6⟩ := checks
  have r1 := absDiff_bound _ _ _ c1
  have r2 := absDiff_bound _ _ _ c2
  have r3 := absDiff_bound _ _ _ c3
  have r4 := absDiff_bound _ _ _ c4
  have r5 := absDiff_bound _ _ _ c5
  have r6 := absDiff_bound _ _ _ c6
  push_cast at r1 r2 r3 r4 r5 r6
  obtain ⟨ha,ha1,hb,hb1⟩ := hi
  obtain ⟨htri,hab,hbS⟩ := hd
  have hS : (0:ℝ)<s := by norm_num [s]
  have ha0 : 0 ≤ a := le_trans (by positivity : (0:ℝ) ≤ box.al) ha
  have hb0 : 0 ≤ b := le_trans (by positivity : (0:ℝ) ≤ box.bl) hb
  let L := (box.al:ℝ)+(box.bl:ℝ)+(s:ℝ)
  let V := a+b+(s:ℝ)
  have hLV : L ≤ V := by dsimp [L,V]; linarith only [ha,hb]
  have hV : 0 < V := by dsimp [V]; linarith
  have hsumne : a+b+(s:ℝ) ≠ 0 := ne_of_gt hV
  have hA : |2*a-b-(s:ℝ)| ≤ L/10 := by
    apply abs_between ((2:ℝ)*box.al-((box.bh:ℝ)+s)) (2*(box.ah:ℝ)-((box.bl:ℝ)+s)) _ _
      (by linarith only [ha,hb1]) (by linarith only [ha1,hb])
    · exact r1
    · exact r2
  have hB : |2*b-a-(s:ℝ)| ≤ L/10 := by
    apply abs_between ((2:ℝ)*box.bl-((box.ah:ℝ)+s)) (2*(box.bh:ℝ)-((box.al:ℝ)+s)) _ _
      (by linarith only [hb,ha1]) (by linarith only [hb1,ha])
    · exact r3
    · exact r4
  have hC : |2*(s:ℝ)-a-b| ≤ L/10 := by
    apply abs_between (2*(s:ℝ)-((box.ah:ℝ)+box.bh)) (2*(s:ℝ)-((box.al:ℝ)+box.bl)) _ _
      (by linarith only [ha1,hb1]) (by linarith only [ha,hb])
    · exact r5
    · exact r6
  apply mean_equality a b s (by dsimp [V] at hV; linarith only [hV]) he
  · have heq : a/((a+b+(s:ℝ))/3)-1=(2*a-b-(s:ℝ))/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hA
  · have heq : b/((a+b+(s:ℝ))/3)-1=(2*b-a-(s:ℝ))/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hB
  · have heq : (s:ℝ)/((a+b+(s:ℝ))/3)-1=(2*(s:ℝ)-a-b)/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hC

theorem interval_leaf_equality (box : Box) (ma mb mc wa wb wc : ℕ) (a b : ℝ)
    (hcheck : intervalCheck box ma mb mc wa wb wc=true)
    (hi : InBox box a b) (hd : Domain a b) : defect a b s=0 → a=b ∧ b=(s:ℝ) := by
  intro he
  have hh := interval_leaf_strict box ma mb mc wa wb wc a b hcheck hi hd
  rw [he] at hh
  exact False.elim (lt_irrefl 0 hh)

theorem certificate_equality (a b : ℝ) (hi : InBox root a b) (hd : Domain a b)
    (he : defect a b s=0) : a=b ∧ b=(s:ℝ) :=
  verified_cover (fun a b => defect a b s=0 → a=b ∧ b=(s:ℝ))
    local_leaf_equality interval_leaf_equality a b hi hd he

theorem sorted_triangle_equality (a b c : ℝ)
    (ha : 0<a) (hab : a≤b) (hbc : b≤c) (htri : c≤a+b) (he : defect a b c=0) : a=b ∧ b=c := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hc : 0<c := lt_of_lt_of_le hb hbc
  have hS : (0:ℝ)<s := by norm_num [s]
  let t := (s:ℝ)/c
  have ht : 0<t := div_pos hS hc
  have htc : t*c=(s:ℝ) := by dsimp [t]; field_simp
  have hab' : t*a≤t*b := mul_le_mul_of_nonneg_left hab (le_of_lt ht)
  have hb' : t*b≤(s:ℝ) := by rw [← htc]; exact mul_le_mul_of_nonneg_left hbc (le_of_lt ht)
  have ha' : t*a≤(s:ℝ) := le_trans hab' hb'
  have htri' : (s:ℝ)≤t*a+t*b := by
    rw [← htc,← mul_add]
    exact mul_le_mul_of_nonneg_left htri (le_of_lt ht)
  have hhalf : ((s/2:ℕ):ℝ)=(s:ℝ)/2 := by norm_num [s]
  have hi : InBox root (t*a) (t*b) := by
    simp only [InBox,root,Nat.cast_zero]
    rw [hhalf]
    exact ⟨le_of_lt (mul_pos ht ha),ha',by linarith only [hab',htri'],hb'⟩
  have hd : Domain (t*a) (t*b) := ⟨htri',hab',hb'⟩
  have heScaled := defect_scale t a b c ht
    (ne_of_gt (add_pos ha hb)) (ne_of_gt (add_pos hb hc)) (ne_of_gt (add_pos hc ha))
  rw [htc,he,mul_zero] at heScaled
  have normalized := certificate_equality (t*a) (t*b) hi hd heScaled
  have h1 : t*a=t*b := normalized.1
  have h2 : t*b=t*c := normalized.2.trans htc.symm
  exact ⟨mul_left_cancel₀ (ne_of_gt ht) h1,mul_left_cancel₀ (ne_of_gt ht) h2⟩

theorem defect_cycle (a b c : ℝ) : defect a b c=defect b c a := by
  unfold defect
  ring

theorem defect_swap (a b c : ℝ) : defect a b c=defect b a c := by
  unfold defect
  rw [bisector_symm b a c,bisector_symm a c b,bisector_symm c b a,
    median_symm b a c,median_symm a c b,median_symm c b a]
  ring

theorem defect_swap_last (a b c : ℝ) : defect a b c=defect a c b := by
  calc
    _ = defect b c a := defect_cycle a b c
    _ = defect c a b := defect_cycle b c a
    _ = defect a c b := defect_swap c a b

theorem equality_only_equilateral (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (habc : c<a+b) (hbca : a<b+c) (hcab : b<c+a)
    (he : defect a b c=0) : a=b ∧ b=c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact sorted_triangle_equality a b c ha hab hbc (le_of_lt habc) he
    · rcases le_total a c with hac | hca
      · have he' : defect a c b=0 := by rw [defect_swap_last a c b]; exact he
        have hh := sorted_triangle_equality a c b ha hac hcb (by linarith only [hcab]) he'
        constructor <;> linarith only [hh.1,hh.2]
      · have he' : defect c a b=0 := by rw [defect_cycle c a b]; exact he
        have hh := sorted_triangle_equality c a b hc hca hab (le_of_lt hcab) he'
        constructor <;> linarith only [hh.1,hh.2]
  · rcases le_total a c with hac | hca
    · have he' : defect b a c=0 := by rw [defect_swap b a c]; exact he
      have hh := sorted_triangle_equality b a c hb hba hac (by linarith only [habc]) he'
      constructor <;> linarith only [hh.1,hh.2]
    · rcases le_total b c with hbc | hcb
      · have he' : defect b c a=0 := by rw [defect_cycle b c a,defect_cycle c a b]; exact he
        have hh := sorted_triangle_equality b c a hb hbc hca (le_of_lt hbca) he'
        constructor <;> linarith only [hh.1,hh.2]
      · have he' : defect c b a=0 := by rw [defect_swap c b a,defect_cycle b c a,defect_cycle c a b]; exact he
        have hh := sorted_triangle_equality c b a hc hcb hba (by linarith only [hbca]) he'
        constructor <;> linarith only [hh.1,hh.2]

theorem equilateral_equality (a : ℝ) (ha : 0<a) : defect a a a=0 := by
  have hm : median 1 1 1=Real.sqrt (3/4:ℝ) := by norm_num [median]
  have hw : bisector 1 1 1=Real.sqrt (3/4:ℝ) := by norm_num [bisector]
  have hk2 : (Real.sqrt (3/4:ℝ))^2=3/4 := Real.sq_sqrt (by norm_num)
  have hk4 : (Real.sqrt (3/4:ℝ))^4=9/16 := by nlinarith only [hk2,sq_nonneg ((Real.sqrt (3/4:ℝ))^2-3/4)]
  have hu : defect 1 1 1=0 := by
    unfold defect
    rw [hm,hw]
    calc
      _ = 9*(Real.sqrt (3/4:ℝ))^4-81/16 := by ring
      _ = 0 := by rw [hk4]; norm_num
  have hh := defect_scale a 1 1 1 ha (by norm_num) (by norm_num) (by norm_num)
  simpa only [mul_one,hu,mul_zero] using hh

theorem equality_iff_equilateral (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (habc : c<a+b) (hbca : a<b+c) (hcab : b<c+a) :
    ((bisector a b c+bisector b c a+bisector c a b)*
      ((median a b c)^3+(median b c a)^3+(median c a b)^3)=((a+b+c)/2)^4) ↔
      a=b ∧ b=c := by
  constructor
  · intro he
    apply equality_only_equilateral a b c ha hb hc habc hbca hcab
    exact sub_eq_zero.mpr he
  · rintro ⟨hab,hbc⟩
    subst b
    subst c
    exact sub_eq_zero.mp (equilateral_equality a ha)

#print axioms equality_iff_equilateral
#print axioms sorted_triangle_equality
#print axioms certificate_equality
#print axioms local_equality
#print axioms mean_equality
end LiuEquality
