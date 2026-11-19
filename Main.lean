import RealBounds
import CheckerCoverage

namespace LiuMain
open LiuCertificate LiuReal

def Claim (a b c : ℝ) : Prop :=
  ((a+b+c)/2)^4 ≤ (bisector a b c+bisector b c a+bisector c a b)*
    ((median a b c)^3+(median b c a)^3+(median c a b)^3)

theorem interval_leaf_sound (box : Box) (ma mb mc wa wb wc : ℕ) (a b : ℝ)
    (hcheck : intervalCheck box ma mb mc wa wb wc = true)
    (hi : InBox box a b) (hd : Domain a b) : Claim a b s := by
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
  exact le_of_lt (certified_triangle_interval a b s q box.al box.ah box.bl box.bh ma mb mc wa wb wc
    (by decide) (by decide) ha ha1 hb hb1 hab hbS htri hma hmb hmc hwa hwb hwc hprod)

theorem median_scale (t a b c : ℝ) (ht : 0 < t) :
    median (t*a) (t*b) (t*c) = t*median a b c := by
  unfold median
  rw [show (2*(t*b)^2+2*(t*c)^2-(t*a)^2)/4 = t^2*((2*b^2+2*c^2-a^2)/4) by ring]
  rw [Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq_eq_abs,abs_of_pos ht]

theorem bisector_scale (t a b c : ℝ) (ht : 0 < t) (hbc : b+c ≠ 0) :
    bisector (t*a) (t*b) (t*c) = t*bisector a b c := by
  unfold bisector
  have hid : (t*b)*(t*c)*(t*a+t*b+t*c)*(t*b+t*c-t*a)/(t*b+t*c)^2 =
      t^2*(b*c*(a+b+c)*(b+c-a)/(b+c)^2) := by
    rw [show t*b+t*c=t*(b+c) by ring]
    field_simp
    <;> ring
  rw [hid,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq_eq_abs,abs_of_pos ht]

theorem claim_scale (t a b c : ℝ) (ht : 0 < t)
    (hab : a+b ≠ 0) (hbc : b+c ≠ 0) (hca : c+a ≠ 0)
    (h : Claim a b c) : Claim (t*a) (t*b) (t*c) := by
  unfold Claim at *
  rw [median_scale t a b c ht,median_scale t b c a ht,median_scale t c a b ht,
    bisector_scale t a b c ht hbc,bisector_scale t b c a ht hca,bisector_scale t c a b ht hab]
  have scaled := mul_le_mul_of_nonneg_left h (pow_nonneg (le_of_lt ht) 4)
  convert scaled using 1 <;> ring

theorem local_claim (p q r : ℝ) (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    Claim (1+p) (1+q) (1+r) := by
  have hsum : ((1+p)+(1+q)+(1+r))/2=(3/2:ℝ) := by linarith
  unfold Claim
  rw [hsum]
  norm_num only [show (3/2:ℝ)^4=81/16 by norm_num]
  exact local_triangle_inequality p q r hs hp hq hr

theorem positive_one_add (x : ℝ) (h : |x| ≤ 1/10) : 0 < 1+x := by
  have hx := (abs_le.mp h).1
  linarith only [hx]

theorem mean_neighborhood (a b c : ℝ) (ht : 0 < (a+b+c)/3)
    (hp : |a/((a+b+c)/3)-1| ≤ 1/10)
    (hq : |b/((a+b+c)/3)-1| ≤ 1/10)
    (hr : |c/((a+b+c)/3)-1| ≤ 1/10) : Claim a b c := by
  let t := (a+b+c)/3
  let p := a/t-1
  let q := b/t-1
  let r := c/t-1
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htSum : a+b+c=3*t := by dsimp [t]; ring
  have hs : p+q+r=0 := by
    dsimp only [p,q,r]
    field_simp [ht0]
    <;> nlinarith only [htSum]
  have h1 := local_claim p q r hs hp hq hr
  have pp := positive_one_add p hp
  have pq := positive_one_add q hq
  have pr := positive_one_add r hr
  have scaled := claim_scale t (1+p) (1+q) (1+r) ht
    (ne_of_gt (add_pos pp pq)) (ne_of_gt (add_pos pq pr)) (ne_of_gt (add_pos pr pp)) h1
  have ha : t*(1+p)=a := by dsimp only [p]; field_simp [ht0] <;> ring
  have hb : t*(1+q)=b := by dsimp only [q]; field_simp [ht0] <;> ring
  have hc : t*(1+r)=c := by dsimp only [r]; field_simp [ht0] <;> ring
  simpa only [ha,hb,hc] using scaled

theorem absDiff_cast (x y : ℕ) :
    ((absDiff x y:ℕ):ℝ) = |(x:ℝ)-(y:ℝ)| := by
  unfold absDiff
  rw [Nat.cast_add,nat_sub_cast_max,nat_sub_cast_max]
  by_cases h : (y:ℝ) ≤ x
  · rw [max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h),abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · have hh : (x:ℝ) ≤ y := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left (sub_nonpos.mpr hh),max_eq_right (sub_nonneg.mpr hh),abs_of_nonpos (sub_nonpos.mpr hh)]
    ring

theorem absDiff_bound (x y N : ℕ) (h : 10*absDiff x y ≤ N) :
    |(x:ℝ)-(y:ℝ)| ≤ (N:ℝ)/10 := by
  have hh : 10*((absDiff x y:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast h
  rw [absDiff_cast] at hh
  linarith only [hh]

theorem abs_between (lo hi x B : ℝ) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hblo : |lo| ≤ B) (hbhi : |hi| ≤ B) : |x| ≤ B := by
  obtain ⟨hl0,hl1⟩ := abs_le.mp hblo
  obtain ⟨hh0,hh1⟩ := abs_le.mp hbhi
  apply abs_le.mpr
  constructor <;> linarith

theorem small_ratio (x L V : ℝ) (hV : 0<V) (hLV : L≤V) (hx : |x|≤L/10) : |x/V|≤1/10 := by
  rw [abs_div,abs_of_pos hV]
  apply (div_le_iff₀ hV).2
  linarith only [hLV,hx]

theorem local_leaf_sound (box : Box) (a b : ℝ)
    (hcheck : localCheck box = true) (hi : InBox box a b) (hd : Domain a b) : Claim a b s := by
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
  apply mean_neighborhood a b s (by dsimp [V] at hV; linarith only [hV])
  · have heq : a/((a+b+(s:ℝ))/3)-1=(2*a-b-(s:ℝ))/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hA
  · have heq : b/((a+b+(s:ℝ))/3)-1=(2*b-a-(s:ℝ))/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hB
  · have heq : (s:ℝ)/((a+b+(s:ℝ))/3)-1=(2*(s:ℝ)-a-b)/V := by dsimp only [V]; field_simp [hsumne] <;> ring
    rw [heq]
    exact small_ratio _ L V hV hLV hC

theorem sorted_certificate_theorem (a b : ℝ) (hi : InBox root a b) (hd : Domain a b) : Claim a b s :=
  verified_cover (fun a b => Claim a b s) local_leaf_sound interval_leaf_sound a b hi hd

theorem sorted_triangle_theorem (a b c : ℝ)
    (ha : 0<a) (hab : a≤b) (hbc : b≤c) (htri : c≤a+b) : Claim a b c := by
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
  have normalized := sorted_certificate_theorem (t*a) (t*b) hi hd
  have back := claim_scale (1/t) (t*a) (t*b) (s:ℝ) (one_div_pos.mpr ht)
    (ne_of_gt (add_pos (mul_pos ht ha) (mul_pos ht hb)))
    (ne_of_gt (add_pos (mul_pos ht hb) hS))
    (ne_of_gt (add_pos hS (mul_pos ht ha))) normalized
  have hta : (1/t)*(t*a)=a := by field_simp
  have htb : (1/t)*(t*b)=b := by field_simp
  have hts : (1/t)*(s:ℝ)=c := by rw [← htc]; field_simp
  simpa only [hta,htb,hts] using back

theorem median_symm (a b c : ℝ) : median a b c = median a c b := by
  unfold median
  congr 1
  ring

theorem bisector_symm (a b c : ℝ) : bisector a b c = bisector a c b := by
  unfold bisector
  congr 1
  ring

theorem claim_swap (a b c : ℝ) : Claim a b c ↔ Claim b a c := by
  unfold Claim
  rw [bisector_symm b a c,bisector_symm a c b,bisector_symm c b a,
    median_symm b a c,median_symm a c b,median_symm c b a]
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem claim_cycle (a b c : ℝ) : Claim a b c ↔ Claim b c a := by
  unfold Claim
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem liu_conjecture_5_1 (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (habc : c<a+b) (hbca : a<b+c) (hcab : b<c+a) : Claim a b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact sorted_triangle_theorem a b c ha hab hbc (by linarith only [habc])
    · rcases le_total a c with hac | hca
      · have hh := sorted_triangle_theorem a c b ha hac hcb (by linarith only [hcab])
        exact (claim_swap a b c).mpr ((claim_cycle c b a).mp ((claim_cycle a c b).mp hh))
      · have hh := sorted_triangle_theorem c a b hc hca hab (by linarith only [hcab])
        exact (claim_cycle c a b).mp hh
  · rcases le_total a c with hac | hca
    · exact (claim_swap a b c).mpr (sorted_triangle_theorem b a c hb hba hac (by linarith only [habc]))
    · rcases le_total b c with hbc | hcb
      · have hh := sorted_triangle_theorem b c a hb hbc hca (by linarith only [hbca])
        exact (claim_cycle a b c).mpr hh
      · have hh := sorted_triangle_theorem c b a hc hcb hba (by linarith only [hbca])
        exact (claim_swap a b c).mpr ((claim_cycle c b a).mp hh)

#print axioms liu_conjecture_5_1
#print axioms sorted_triangle_theorem
#print axioms sorted_certificate_theorem
#print axioms local_leaf_sound
#print axioms mean_neighborhood
#print axioms interval_leaf_sound
end LiuMain
