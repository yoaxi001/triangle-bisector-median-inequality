import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option maxHeartbeats 400000

namespace LiuReal
noncomputable section

def median (a b c : ℝ) : ℝ := Real.sqrt ((2*b^2+2*c^2-a^2)/4)
def bisector (a b c : ℝ) : ℝ :=
  Real.sqrt (b*c*(a+b+c)*(b+c-a)/(b+c)^2)

theorem lower_from_square (x y : ℝ) (hy : 0 ≤ y) (h : x^2 ≤ y) :
    x ≤ Real.sqrt y := by
  have hs := Real.sq_sqrt hy
  have hn := Real.sqrt_nonneg y
  nlinarith [sq_nonneg (x - Real.sqrt y)]

theorem sqrt_lower (x : ℝ) (hl : -(1/4:ℝ) ≤ x) (hu : x ≤ 1/4) :
    1+x/2-x^2/6 ≤ Real.sqrt (1+x) := by
  have hx : x^2 ≤ 1/16 := by nlinarith [mul_nonneg (by linarith : 0 ≤ x+1/4) (by linarith : 0 ≤ 1/4-x)]
  have hb : 0 ≤ 1/12+x/6-x^2/36 := by linarith
  have hid : (1+x)-(1+x/2-x^2/6)^2 = x^2*(1/12+x/6-x^2/36) := by ring
  apply lower_from_square
  · linarith
  · nlinarith [mul_nonneg (sq_nonneg x) hb]

theorem sqrt_cube_lower (x : ℝ) (hl : -(1/4:ℝ) ≤ x) (hu : x ≤ 1/4) :
    1+3*x/2+x^2/3 ≤ (Real.sqrt (1+x))^3 := by
  have hx : x^2 ≤ 1/16 := by nlinarith [mul_nonneg (by linarith : 0 ≤ x+1/4) (by linarith : 0 ≤ 1/4-x)]
  have hb : 0 ≤ 1/12-x^2/9 := by linarith
  have hid : (1+x)^3-(1+3*x/2+x^2/3)^2 = x^2*(1/12-x^2/9) := by ring
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1+x)
  have hn := Real.sqrt_nonneg (1+x)
  have hc : ((Real.sqrt (1+x))^3)^2 = (1+x)^3 := by
    calc
      _ = ((Real.sqrt (1+x))^2)^3 := by ring
      _ = (1+x)^3 := by rw [hs]
  have hp : 0 ≤ (Real.sqrt (1+x))^3 := pow_nonneg hn _
  nlinarith [mul_nonneg (sq_nonneg x) hb,
    sq_nonneg ((Real.sqrt (1+x))^3-(1+3*x/2+x^2/3))]

theorem local_product_bound (T W M : ℝ)
    (hT : 0 ≤ T) (hTupper : T ≤ 3/100)
    (hw : 3-4*T/3 ≤ W) (hm : 3+7*T/3 ≤ M) :
    9 ≤ W*M := by
  have hwp : 0 ≤ 3-4*T/3 := by linarith
  have hmp : 0 ≤ 3+7*T/3 := by linarith
  have hmul := mul_le_mul hw hm hmp (le_trans hwp hw)
  have ht : 0 ≤ T*(3-28*T/9) := mul_nonneg hT (by linarith)
  nlinarith

-- The finite certificate supplies lower bounds for six actual lengths.
-- This theorem assembles those bounds into the desired product bound.
theorem assemble_bounds
    (ma mb mc wa wb wc la lb lc da db dc s : ℝ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) (hdc : 0 ≤ dc)
    (hma : la ≤ ma) (hmb : lb ≤ mb) (hmc : lc ≤ mc)
    (hwa : da ≤ wa) (hwb : db ≤ wb) (hwc : dc ≤ wc)
    (hcert : s^4 < (da+db+dc)*(la^3+lb^3+lc^3)) :
    s^4 < (wa+wb+wc)*(ma^3+mb^3+mc^3) := by
  have hma3 := pow_le_pow_left₀ hla hma 3
  have hmb3 := pow_le_pow_left₀ hlb hmb 3
  have hmc3 := pow_le_pow_left₀ hlc hmc 3
  have hsum : la^3+lb^3+lc^3 ≤ ma^3+mb^3+mc^3 := by linarith
  have hwsum : da+db+dc ≤ wa+wb+wc := by linarith
  have hlo : 0 ≤ la^3+lb^3+lc^3 := by positivity
  have hwo : 0 ≤ wa+wb+wc := by linarith
  exact lt_of_lt_of_le hcert (mul_le_mul hwsum hsum hlo hwo)

theorem normalized_median_identity (p q r : ℝ) (hs : p+q+r=0) :
    (2*(1+q)^2+2*(1+r)^2-(1+p)^2)/4 =
      (3/4:ℝ)*(1-2*p+(2/3)*(p^2+q^2+r^2)-p^2) := by
  nlinarith

theorem normalized_bisector_identity (p q r : ℝ)
    (hs : p+q+r=0) (hp : p ≠ 2) :
    (1+q)*(1+r)*((1+p)+(1+q)+(1+r))*((1+q)+(1+r)-(1+p)) /
        ((1+q)+(1+r))^2 =
      (3/4:ℝ)*(1-2*p-(1-2*p)/(2-p)^2*(q-r)^2) := by
  have hr : r = -p-q := by linarith
  subst r
  have hd : (2:ℝ)-p ≠ 0 := by intro h; apply hp; linarith
  have hsum : (1:ℝ)+q+(1+(-p-q)) = 2-p := by ring
  rw [hsum]
  field_simp
  <;> ring

theorem perturbation_bounds (p q r : ℝ)
    (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    0 ≤ p^2+q^2+r^2 ∧ p^2+q^2+r^2 ≤ 3/100 ∧
    -(1/4:ℝ) ≤ -2*p+(2/3)*(p^2+q^2+r^2)-p^2 ∧
    -2*p+(2/3)*(p^2+q^2+r^2)-p^2 ≤ 1/4 := by
  obtain ⟨hp0,hp1⟩ := abs_le.mp hp
  obtain ⟨hq0,hq1⟩ := abs_le.mp hq
  obtain ⟨hr0,hr1⟩ := abs_le.mp hr
  have hp2 : p^2 ≤ 1/100 := by nlinarith [mul_nonneg (by linarith : 0 ≤ p+1/10) (by linarith : 0 ≤ 1/10-p)]
  have hq2 : q^2 ≤ 1/100 := by nlinarith [mul_nonneg (by linarith : 0 ≤ q+1/10) (by linarith : 0 ≤ 1/10-q)]
  have hr2 : r^2 ≤ 1/100 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r+1/10) (by linarith : 0 ≤ 1/10-r)]
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> nlinarith [sq_nonneg p,sq_nonneg q,sq_nonneg r]

theorem bisector_loss_bounds (p q r : ℝ)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    let D := (q-r)^2
    let z := (1-2*p)/(2-p)^2*D
    0 ≤ z ∧ z ≤ D/3 ∧ z^2 ≤ D/225 ∧
    -(1/4:ℝ) ≤ -2*p-z ∧ -2*p-z ≤ 1/4 ∧
    (-2*p-z)^2 ≤ 5*p^2+5*z^2 := by
  dsimp
  obtain ⟨hp0,hp1⟩ := abs_le.mp hp
  obtain ⟨hq0,hq1⟩ := abs_le.mp hq
  obtain ⟨hr0,hr1⟩ := abs_le.mp hr
  have hd : 0 < (2-p)^2 := sq_pos_of_pos (by linarith)
  have hk0 : 0 ≤ (1-2*p)/(2-p)^2 := div_nonneg (by linarith) (le_of_lt hd)
  have hk1 : (1-2*p)/(2-p)^2 ≤ (1/3:ℝ) := by
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (1+p)]
  have hD : (q-r)^2 ≤ 1/25 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ q-r+1/5) (by linarith : 0 ≤ 1/5-(q-r))]
  have hz0 := mul_nonneg hk0 (sq_nonneg (q-r))
  have hz1 := mul_le_mul_of_nonneg_right hk1 (sq_nonneg (q-r))
  have hzsmall : (1-2*p)/(2-p)^2*(q-r)^2 ≤ 1/75 := by nlinarith
  have hz2 := mul_le_mul_of_nonneg_left hzsmall hz0
  have hzsq : ((1-2*p)/(2-p)^2*(q-r)^2)^2 ≤ (q-r)^2/225 := by nlinarith
  refine ⟨hz0, ?_, hzsq, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · nlinarith [sq_nonneg (p-2*((1-2*p)/(2-p)^2*(q-r)^2))]

theorem median_interval_lower (a b c al ah bl bh cl ch L : ℝ)
    (ha : al ≤ a) (ha1 : a ≤ ah) (hb : bl ≤ b) (hc : cl ≤ c)
    (hal : 0 ≤ al) (hbl : 0 ≤ bl) (hcl : 0 ≤ cl)
    (hL : 4*L^2 ≤ 2*bl^2+2*cl^2-ah^2) :
    L ≤ median a b c := by
  have haa : a^2 ≤ ah^2 := pow_le_pow_left₀ (le_trans hal ha) ha1 2
  have hbb : bl^2 ≤ b^2 := pow_le_pow_left₀ hbl hb 2
  have hcc : cl^2 ≤ c^2 := pow_le_pow_left₀ hcl hc 2
  have hrad : L^2 ≤ (2*b^2+2*c^2-a^2)/4 := by linarith
  apply lower_from_square
  · nlinarith [sq_nonneg L]
  · exact hrad

theorem rational_radical_lower (L numerator denominator : ℝ)
    (hd : 0 < denominator) (hnum : 0 ≤ numerator)
    (h : L^2*denominator ≤ numerator) :
    L ≤ Real.sqrt (numerator/denominator) := by
  apply lower_from_square
  · exact div_nonneg hnum (le_of_lt hd)
  · exact (le_div_iff₀ hd).2 h

theorem aggregate_local_bounds (T u v w d e f : ℝ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 3/100)
    (hu : |u| ≤ 1/4) (hv : |v| ≤ 1/4) (hw : |w| ≤ 1/4)
    (hd : |d| ≤ 1/4) (he : |e| ≤ 1/4) (hf : |f| ≤ 1/4)
    (husum : u+v+w=T) (hdsum : -T ≤ d+e+f)
    (hdsq : d^2+e^2+f^2 ≤ (11/2)*T) :
    9 ≤ (Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f))*
      ((Real.sqrt (1+u))^3+(Real.sqrt (1+v))^3+(Real.sqrt (1+w))^3) := by
  have mu := sqrt_cube_lower u (abs_le.mp hu).1 (abs_le.mp hu).2
  have mv := sqrt_cube_lower v (abs_le.mp hv).1 (abs_le.mp hv).2
  have mw := sqrt_cube_lower w (abs_le.mp hw).1 (abs_le.mp hw).2
  have wd := sqrt_lower d (abs_le.mp hd).1 (abs_le.mp hd).2
  have we := sqrt_lower e (abs_le.mp he).1 (abs_le.mp he).2
  have wf := sqrt_lower f (abs_le.mp hf).1 (abs_le.mp hf).2
  have hm : 3+(3/2)*T ≤ (Real.sqrt (1+u))^3+(Real.sqrt (1+v))^3+(Real.sqrt (1+w))^3 := by
    nlinarith only [mu,mv,mw,husum,sq_nonneg u,sq_nonneg v,sq_nonneg w]
  have hl : 3-(17/12)*T ≤ Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f) := by
    linarith only [wd,we,wf,hdsum,hdsq]
  have hm0 : 0 ≤ 3+(3/2)*T := by linarith only [hT0]
  have hl0 : 0 ≤ Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f) := by
    linarith only [hl,hT1]
  have hprod := mul_le_mul hl hm hm0 hl0
  have hrem := mul_nonneg hT0 (by linarith only [hT1] : 0 ≤ 1/4-(17/8)*T)
  nlinarith only [hprod,hrem]

theorem aggregate_local_bounds_gap (T u v w d e f : ℝ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 3/100)
    (hu : |u| ≤ 1/4) (hv : |v| ≤ 1/4) (hw : |w| ≤ 1/4)
    (hd : |d| ≤ 1/4) (he : |e| ≤ 1/4) (hf : |f| ≤ 1/4)
    (husum : u+v+w=T) (hdsum : -T ≤ d+e+f)
    (hdsq : d^2+e^2+f^2 ≤ (11/2)*T) :
    9+T/8 ≤ (Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f))*
      ((Real.sqrt (1+u))^3+(Real.sqrt (1+v))^3+(Real.sqrt (1+w))^3) := by
  have mu := sqrt_cube_lower u (abs_le.mp hu).1 (abs_le.mp hu).2
  have mv := sqrt_cube_lower v (abs_le.mp hv).1 (abs_le.mp hv).2
  have mw := sqrt_cube_lower w (abs_le.mp hw).1 (abs_le.mp hw).2
  have wd := sqrt_lower d (abs_le.mp hd).1 (abs_le.mp hd).2
  have we := sqrt_lower e (abs_le.mp he).1 (abs_le.mp he).2
  have wf := sqrt_lower f (abs_le.mp hf).1 (abs_le.mp hf).2
  have hm : 3+(3/2)*T ≤ (Real.sqrt (1+u))^3+(Real.sqrt (1+v))^3+(Real.sqrt (1+w))^3 := by
    nlinarith only [mu,mv,mw,husum,sq_nonneg u,sq_nonneg v,sq_nonneg w]
  have hl : 3-(17/12)*T ≤ Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f) := by
    linarith only [wd,we,wf,hdsum,hdsq]
  have hm0 : 0 ≤ 3+(3/2)*T := by linarith only [hT0]
  have hl0 : 0 ≤ Real.sqrt (1+d)+Real.sqrt (1+e)+Real.sqrt (1+f) := by
    linarith only [hl,hT1]
  have hprod := mul_le_mul hl hm hm0 hl0
  have hrem := mul_nonneg hT0 (by linarith only [hT1] : 0 ≤ 1/8-(17/8)*T)
  nlinarith only [hprod,hrem]

theorem local_radical_product (p q r : ℝ)
    (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    let T := p^2+q^2+r^2
    let u := fun x => -2*x+(2/3)*T-x^2
    let d := fun x y z => -2*x-(1-2*x)/(2-x)^2*(y-z)^2
    9 ≤ (Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q)) *
      ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3) := by
  let T := p^2+q^2+r^2
  let up := -2*p+(2/3)*T-p^2
  let uq := -2*q+(2/3)*T-q^2
  let ur := -2*r+(2/3)*T-r^2
  let zp := (1-2*p)/(2-p)^2*(q-r)^2
  let zq := (1-2*q)/(2-q)^2*(r-p)^2
  let zr := (1-2*r)/(2-r)^2*(p-q)^2
  have hs1 : q+r+p=0 := by linarith
  have hs2 : r+p+q=0 := by linarith
  have bu := perturbation_bounds p q r hs hp hq hr
  have bv := perturbation_bounds q r p hs1 hq hr hp
  have bw := perturbation_bounds r p q hs2 hr hp hq
  have bp := bisector_loss_bounds p q r hp hq hr
  have bq := bisector_loss_bounds q r p hq hr hp
  have br := bisector_loss_bounds r p q hr hp hq
  have hT0 : 0 ≤ T := bu.1
  have hT1 : T ≤ 3/100 := bu.2.1
  have hup : |up| ≤ 1/4 := abs_le.mpr bu.2.2
  have huq : |uq| ≤ 1/4 := by
    apply abs_le.mpr
    dsimp [uq,T]
    convert bv.2.2 using 1 <;> ring
  have hur : |ur| ≤ 1/4 := by
    apply abs_le.mpr
    dsimp [ur,T]
    convert bw.2.2 using 1 <;> ring
  have hdp : |-2*p-zp| ≤ 1/4 := abs_le.mpr ⟨bp.2.2.2.1,bp.2.2.2.2.1⟩
  have hdq : |-2*q-zq| ≤ 1/4 := abs_le.mpr ⟨bq.2.2.2.1,bq.2.2.2.2.1⟩
  have hdr : |-2*r-zr| ≤ 1/4 := abs_le.mpr ⟨br.2.2.2.1,br.2.2.2.2.1⟩
  have hDp : zp ≤ (q-r)^2/3 := bp.2.1
  have hDq : zq ≤ (r-p)^2/3 := bq.2.1
  have hDr : zr ≤ (p-q)^2/3 := br.2.1
  have hSp : zp^2 ≤ (q-r)^2/225 := bp.2.2.1
  have hSq : zq^2 ≤ (r-p)^2/225 := bq.2.2.1
  have hSr : zr^2 ≤ (p-q)^2/225 := br.2.2.1
  have hLp : (-2*p-zp)^2 ≤ 5*p^2+5*zp^2 := bp.2.2.2.2.2
  have hLq : (-2*q-zq)^2 ≤ 5*q^2+5*zq^2 := bq.2.2.2.2.2
  have hLr : (-2*r-zr)^2 ≤ 5*r^2+5*zr^2 := br.2.2.2.2.2
  have hD : (q-r)^2+(r-p)^2+(p-q)^2=3*T := by
    dsimp [T]
    have hzero : (p+q+r)^2=0 := by rw [hs]; norm_num
    nlinarith only [hzero]
  have hsumz : zp+zq+zr ≤ T := by linarith only [hDp,hDq,hDr,hD]
  have hsumz2 : zp^2+zq^2+zr^2 ≤ T/75 := by
    calc
      _ ≤ (q-r)^2/225+(r-p)^2/225+(p-q)^2/225 := add_le_add (add_le_add hSp hSq) hSr
      _ = ((q-r)^2+(r-p)^2+(p-q)^2)/225 := by ring
      _ = T/75 := by rw [hD]; ring
  have hsumd : -T ≤ (-2*p-zp)+(-2*q-zq)+(-2*r-zr) := by linarith only [hs,hsumz]
  have hTeq : T=p^2+q^2+r^2 := rfl
  have hsumd2 : (-2*p-zp)^2+(-2*q-zq)^2+(-2*r-zr)^2 ≤ (11/2)*T := by
    linarith only [hLp,hLq,hLr,hsumz2,hTeq,hT0]
  have husum : up+uq+ur=T := by dsimp [up,uq,ur,T]; nlinarith only [hs]
  exact aggregate_local_bounds T up uq ur (-2*p-zp) (-2*q-zq) (-2*r-zr)
    hT0 hT1 hup huq hur hdp hdq hdr husum hsumd hsumd2

theorem local_radical_product_gap (p q r : ℝ)
    (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    let T := p^2+q^2+r^2
    let u := fun x => -2*x+(2/3)*T-x^2
    let d := fun x y z => -2*x-(1-2*x)/(2-x)^2*(y-z)^2
    9+T/8 ≤ (Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q)) *
      ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3) := by
  let T := p^2+q^2+r^2
  let up := -2*p+(2/3)*T-p^2
  let uq := -2*q+(2/3)*T-q^2
  let ur := -2*r+(2/3)*T-r^2
  let zp := (1-2*p)/(2-p)^2*(q-r)^2
  let zq := (1-2*q)/(2-q)^2*(r-p)^2
  let zr := (1-2*r)/(2-r)^2*(p-q)^2
  have hs1 : q+r+p=0 := by linarith
  have hs2 : r+p+q=0 := by linarith
  have bu := perturbation_bounds p q r hs hp hq hr
  have bv := perturbation_bounds q r p hs1 hq hr hp
  have bw := perturbation_bounds r p q hs2 hr hp hq
  have bp := bisector_loss_bounds p q r hp hq hr
  have bq := bisector_loss_bounds q r p hq hr hp
  have br := bisector_loss_bounds r p q hr hp hq
  have hT0 : 0 ≤ T := bu.1
  have hT1 : T ≤ 3/100 := bu.2.1
  have hup : |up| ≤ 1/4 := abs_le.mpr bu.2.2
  have huq : |uq| ≤ 1/4 := by
    apply abs_le.mpr
    dsimp [uq,T]
    convert bv.2.2 using 1 <;> ring
  have hur : |ur| ≤ 1/4 := by
    apply abs_le.mpr
    dsimp [ur,T]
    convert bw.2.2 using 1 <;> ring
  have hdp : |-2*p-zp| ≤ 1/4 := abs_le.mpr ⟨bp.2.2.2.1,bp.2.2.2.2.1⟩
  have hdq : |-2*q-zq| ≤ 1/4 := abs_le.mpr ⟨bq.2.2.2.1,bq.2.2.2.2.1⟩
  have hdr : |-2*r-zr| ≤ 1/4 := abs_le.mpr ⟨br.2.2.2.1,br.2.2.2.2.1⟩
  have hDp : zp ≤ (q-r)^2/3 := bp.2.1
  have hDq : zq ≤ (r-p)^2/3 := bq.2.1
  have hDr : zr ≤ (p-q)^2/3 := br.2.1
  have hSp : zp^2 ≤ (q-r)^2/225 := bp.2.2.1
  have hSq : zq^2 ≤ (r-p)^2/225 := bq.2.2.1
  have hSr : zr^2 ≤ (p-q)^2/225 := br.2.2.1
  have hLp : (-2*p-zp)^2 ≤ 5*p^2+5*zp^2 := bp.2.2.2.2.2
  have hLq : (-2*q-zq)^2 ≤ 5*q^2+5*zq^2 := bq.2.2.2.2.2
  have hLr : (-2*r-zr)^2 ≤ 5*r^2+5*zr^2 := br.2.2.2.2.2
  have hD : (q-r)^2+(r-p)^2+(p-q)^2=3*T := by
    dsimp [T]
    have hzero : (p+q+r)^2=0 := by rw [hs]; norm_num
    nlinarith only [hzero]
  have hsumz : zp+zq+zr ≤ T := by linarith only [hDp,hDq,hDr,hD]
  have hsumz2 : zp^2+zq^2+zr^2 ≤ T/75 := by
    calc
      _ ≤ (q-r)^2/225+(r-p)^2/225+(p-q)^2/225 := add_le_add (add_le_add hSp hSq) hSr
      _ = ((q-r)^2+(r-p)^2+(p-q)^2)/225 := by ring
      _ = T/75 := by rw [hD]; ring
  have hsumd : -T ≤ (-2*p-zp)+(-2*q-zq)+(-2*r-zr) := by linarith only [hs,hsumz]
  have hTeq : T=p^2+q^2+r^2 := rfl
  have hsumd2 : (-2*p-zp)^2+(-2*q-zq)^2+(-2*r-zr)^2 ≤ (11/2)*T := by
    linarith only [hLp,hLq,hLr,hsumz2,hTeq,hT0]
  have husum : up+uq+ur=T := by dsimp [up,uq,ur,T]; nlinarith only [hs]
  exact aggregate_local_bounds_gap T up uq ur (-2*p-zp) (-2*q-zq) (-2*r-zr)
    hT0 hT1 hup huq hur hdp hdq hdr husum hsumd hsumd2

theorem median_local_factor (p q r : ℝ) (hs : p+q+r=0) :
    median (1+p) (1+q) (1+r) = Real.sqrt (3/4:ℝ)*
      Real.sqrt (1-2*p+(2/3)*(p^2+q^2+r^2)-p^2) := by
  unfold median
  rw [normalized_median_identity p q r hs]
  exact Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4) _

theorem bisector_local_factor (p q r : ℝ) (hs : p+q+r=0) (hp : p ≠ 2) :
    bisector (1+p) (1+q) (1+r) = Real.sqrt (3/4:ℝ)*
      Real.sqrt (1-2*p-(1-2*p)/(2-p)^2*(q-r)^2) := by
  unfold bisector
  rw [normalized_bisector_identity p q r hs hp]
  exact Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4) _

theorem bisector_interval_lower (a b c al ah bl bh cl ch L : ℝ)
    (ha : al ≤ a) (ha1 : a ≤ ah)
    (hb : bl ≤ b) (hb1 : b ≤ bh) (hc : cl ≤ c) (hc1 : c ≤ ch)
    (hal : 0 ≤ al) (hbl : 0 ≤ bl) (hcl : 0 ≤ cl)
    (htri : 0 ≤ b+c-a) (hden : 0 < b+c)
    (hL : L^2*(bh+ch)^2 ≤ bl*cl*(al+bl+cl)*max 0 (bl+cl-ah)) :
    L ≤ bisector a b c := by
  have hb0 : 0 ≤ b := le_trans hbl hb
  have hc0 : 0 ≤ c := le_trans hcl hc
  have ha0 : 0 ≤ a := le_trans hal ha
  have hdif : max 0 (bl+cl-ah) ≤ b+c-a := by
    apply max_le htri
    linarith
  have hn : bl*cl*(al+bl+cl)*max 0 (bl+cl-ah) ≤ b*c*(a+b+c)*(b+c-a) := by
    gcongr
  have hden2 : (b+c)^2 ≤ (bh+ch)^2 := by
    apply pow_le_pow_left₀ (le_of_lt hden)
    linarith
  have hsq : L^2*(b+c)^2 ≤ b*c*(a+b+c)*(b+c-a) :=
    le_trans (mul_le_mul_of_nonneg_left hden2 (sq_nonneg L)) (le_trans hL hn)
  exact rational_radical_lower L _ _ (sq_pos_of_pos hden)
    (by positivity) hsq

theorem local_triangle_inequality (p q r : ℝ)
    (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    (81/16:ℝ) ≤
      (bisector (1+p) (1+q) (1+r)+bisector (1+q) (1+r) (1+p)+bisector (1+r) (1+p) (1+q))*
      ((median (1+p) (1+q) (1+r))^3+(median (1+q) (1+r) (1+p))^3+(median (1+r) (1+p) (1+q))^3) := by
  let T := p^2+q^2+r^2
  let u := fun (x : ℝ) => -2*x+(2/3)*T-x^2
  let d := fun (x y z : ℝ) => -2*x-(1-2*x)/(2-x)^2*(y-z)^2
  let k := Real.sqrt (3/4:ℝ)
  have hs1 : q+r+p=0 := by linarith
  have hs2 : r+p+q=0 := by linarith
  have hp2 : p ≠ 2 := by have hh := (abs_le.mp hp).2; linarith
  have hq2 : q ≠ 2 := by have hh := (abs_le.mp hq).2; linarith
  have hr2 : r ≠ 2 := by have hh := (abs_le.mp hr).2; linarith
  have htq : q^2+r^2+p^2=p^2+q^2+r^2 := by ring
  have htr : r^2+p^2+q^2=p^2+q^2+r^2 := by ring
  have mp : median (1+p) (1+q) (1+r)=k*Real.sqrt (1+u p) := by
    dsimp [k,u,T]
    rw [median_local_factor p q r hs]
    congr 2 <;> ring
  have mq : median (1+q) (1+r) (1+p)=k*Real.sqrt (1+u q) := by
    have hh := median_local_factor q r p hs1
    rw [htq] at hh
    dsimp [k,u,T]
    rw [hh]
    congr 2 <;> ring
  have mr : median (1+r) (1+p) (1+q)=k*Real.sqrt (1+u r) := by
    have hh := median_local_factor r p q hs2
    rw [htr] at hh
    dsimp [k,u,T]
    rw [hh]
    congr 2 <;> ring
  have wp : bisector (1+p) (1+q) (1+r)=k*Real.sqrt (1+d p q r) := by
    dsimp [k,d]
    rw [bisector_local_factor p q r hs hp2]
    congr 2 <;> ring
  have wq : bisector (1+q) (1+r) (1+p)=k*Real.sqrt (1+d q r p) := by
    dsimp [k,d]
    rw [bisector_local_factor q r p hs1 hq2]
    congr 2 <;> ring
  have wr : bisector (1+r) (1+p) (1+q)=k*Real.sqrt (1+d r p q) := by
    dsimp [k,d]
    rw [bisector_local_factor r p q hs2 hr2]
    congr 2 <;> ring
  have hk2 : k^2=(3/4:ℝ) := Real.sq_sqrt (by norm_num)
  have hk4 : k^4=(9/16:ℝ) := by nlinarith only [sq_nonneg (k^2-3/4),hk2]
  have root := local_radical_product p q r hs hp hq hr
  change 9 ≤ (Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q))*
    ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3) at root
  have scaled := mul_le_mul_of_nonneg_left root (by positivity : 0 ≤ k^4)
  rw [mp,mq,mr,wp,wq,wr]
  calc
    (81/16:ℝ) = k^4*9 := by rw [hk4]; norm_num
    _ ≤ k^4*((Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q))*
      ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3)) := scaled
    _ = _ := by ring

theorem local_triangle_gap (p q r : ℝ)
    (hs : p+q+r=0)
    (hp : |p| ≤ 1/10) (hq : |q| ≤ 1/10) (hr : |r| ≤ 1/10) :
    (81/16:ℝ)+(9/128)*(p^2+q^2+r^2) ≤
      (bisector (1+p) (1+q) (1+r)+bisector (1+q) (1+r) (1+p)+bisector (1+r) (1+p) (1+q))*
      ((median (1+p) (1+q) (1+r))^3+(median (1+q) (1+r) (1+p))^3+(median (1+r) (1+p) (1+q))^3) := by
  let T := p^2+q^2+r^2
  let u := fun (x : ℝ) => -2*x+(2/3)*T-x^2
  let d := fun (x y z : ℝ) => -2*x-(1-2*x)/(2-x)^2*(y-z)^2
  let k := Real.sqrt (3/4:ℝ)
  have hs1 : q+r+p=0 := by linarith
  have hs2 : r+p+q=0 := by linarith
  have hp2 : p ≠ 2 := by have hh := (abs_le.mp hp).2; linarith
  have hq2 : q ≠ 2 := by have hh := (abs_le.mp hq).2; linarith
  have hr2 : r ≠ 2 := by have hh := (abs_le.mp hr).2; linarith
  have htq : q^2+r^2+p^2=p^2+q^2+r^2 := by ring
  have htr : r^2+p^2+q^2=p^2+q^2+r^2 := by ring
  have mp : median (1+p) (1+q) (1+r)=k*Real.sqrt (1+u p) := by
    dsimp [k,u,T]
    rw [median_local_factor p q r hs]
    congr 2 <;> ring
  have mq : median (1+q) (1+r) (1+p)=k*Real.sqrt (1+u q) := by
    have hh := median_local_factor q r p hs1
    rw [htq] at hh
    dsimp [k,u,T]
    rw [hh]
    congr 2 <;> ring
  have mr : median (1+r) (1+p) (1+q)=k*Real.sqrt (1+u r) := by
    have hh := median_local_factor r p q hs2
    rw [htr] at hh
    dsimp [k,u,T]
    rw [hh]
    congr 2 <;> ring
  have wp : bisector (1+p) (1+q) (1+r)=k*Real.sqrt (1+d p q r) := by
    dsimp [k,d]
    rw [bisector_local_factor p q r hs hp2]
    congr 2 <;> ring
  have wq : bisector (1+q) (1+r) (1+p)=k*Real.sqrt (1+d q r p) := by
    dsimp [k,d]
    rw [bisector_local_factor q r p hs1 hq2]
    congr 2 <;> ring
  have wr : bisector (1+r) (1+p) (1+q)=k*Real.sqrt (1+d r p q) := by
    dsimp [k,d]
    rw [bisector_local_factor r p q hs2 hr2]
    congr 2 <;> ring
  have hk2 : k^2=(3/4:ℝ) := Real.sq_sqrt (by norm_num)
  have hk4 : k^4=(9/16:ℝ) := by nlinarith only [sq_nonneg (k^2-3/4),hk2]
  have root := local_radical_product_gap p q r hs hp hq hr
  change 9+T/8 ≤ (Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q))*
    ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3) at root
  have scaled := mul_le_mul_of_nonneg_left root (by positivity : 0 ≤ k^4)
  rw [mp,mq,mr,wp,wq,wr]
  calc
    (81/16:ℝ)+(9/128)*(p^2+q^2+r^2) = k^4*(9+T/8) := by rw [hk4]; dsimp [T]; ring
    _ ≤ k^4*((Real.sqrt (1+d p q r)+Real.sqrt (1+d q r p)+Real.sqrt (1+d r p q))*
      ((Real.sqrt (1+u p))^3+(Real.sqrt (1+u q))^3+(Real.sqrt (1+u r))^3)) := scaled
    _ = _ := by ring

theorem nat_sub_cast_max (a b : ℕ) :
    ((a-b : ℕ) : ℝ) = max 0 ((a:ℝ)-(b:ℝ)) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hab : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le hab, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast hab)

theorem scaled_sqrt_bound (M Q N D : ℕ)
    (hQ : 0 < Q) (hD : 0 < D)
    (h : D*M^2 ≤ Q^2*N) :
    (M:ℝ)/(Q:ℝ) ≤ Real.sqrt ((N:ℝ)/(D:ℝ)) := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hreal : (D:ℝ)*(M:ℝ)^2 ≤ (Q:ℝ)^2*(N:ℝ) := by exact_mod_cast h
  apply rational_radical_lower _ _ _ hDr (by positivity)
  calc
    ((M:ℝ)/(Q:ℝ))^2*(D:ℝ) = ((D:ℝ)*(M:ℝ)^2)/(Q:ℝ)^2 := by ring
    _ ≤ (N:ℝ) := (div_le_iff₀ (sq_pos_of_pos hQr)).2 (by nlinarith only [hreal])

theorem scaled_median_interval (a b c : ℝ)
    (S Q al ah bl bh cl ch M : ℕ) (hS : 0 < S) (hQ : 0 < Q)
    (ha : (al:ℝ) ≤ a) (ha1 : a ≤ (ah:ℝ))
    (hb : (bl:ℝ) ≤ b) (hc : (cl:ℝ) ≤ c)
    (hcheck : 4*S^2*M^2 ≤ Q^2*(2*bl^2+2*cl^2-ah^2)) :
    (S:ℝ)*(M:ℝ)/(Q:ℝ) ≤ median a b c := by
  by_cases hm : M=0
  · simp only [hm,Nat.cast_zero,mul_zero,zero_div]
    exact Real.sqrt_nonneg _
  have hM : 0 < M := by omega
  have hlhs : 0 < 4*S^2*M^2 := by positivity
  have hsub : ah^2 ≤ 2*bl^2+2*cl^2 := by
    by_contra hh
    have hz : 2*bl^2+2*cl^2-ah^2=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz,mul_zero] at hcheck
    omega
  have hreal : 4*(S:ℝ)^2*(M:ℝ)^2 ≤ (Q:ℝ)^2*(2*(bl:ℝ)^2+2*(cl:ℝ)^2-(ah:ℝ)^2) := by
    have hh : ((4*S^2*M^2:ℕ):ℝ) ≤ ((Q^2*(2*bl^2+2*cl^2-ah^2):ℕ):ℝ) := by exact_mod_cast hcheck
    push_cast [Nat.cast_sub hsub] at hh
    exact hh
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hbound : 4*((S:ℝ)*(M:ℝ)/(Q:ℝ))^2 ≤ 2*(bl:ℝ)^2+2*(cl:ℝ)^2-(ah:ℝ)^2 := by
    calc
      _ = (4*(S:ℝ)^2*(M:ℝ)^2)/(Q:ℝ)^2 := by ring
      _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hQr)).2 (by nlinarith only [hreal])
  exact median_interval_lower a b c al ah bl bh cl ch _ ha ha1 hb hc
    (by positivity) (by positivity) (by positivity) hbound

theorem scaled_bisector_interval (a b c : ℝ)
    (S Q al ah bl bh cl ch W : ℕ) (hQ : 0 < Q)
    (ha : (al:ℝ) ≤ a) (ha1 : a ≤ (ah:ℝ))
    (hb : (bl:ℝ) ≤ b) (hb1 : b ≤ (bh:ℝ))
    (hc : (cl:ℝ) ≤ c) (hc1 : c ≤ (ch:ℝ))
    (htri : 0 ≤ b+c-a) (hden : 0 < b+c)
    (hcheck : S^2*(bh+ch)^2*W^2 ≤ Q^2*bl*cl*(al+bl+cl)*(bl+cl-ah)) :
    (S:ℝ)*(W:ℝ)/(Q:ℝ) ≤ bisector a b c := by
  have hreal : (S:ℝ)^2*((bh:ℝ)+(ch:ℝ))^2*(W:ℝ)^2 ≤
      (Q:ℝ)^2*(bl:ℝ)*(cl:ℝ)*((al:ℝ)+(bl:ℝ)+(cl:ℝ))*max 0 ((bl:ℝ)+(cl:ℝ)-(ah:ℝ)) := by
    have hh : ((S^2*(bh+ch)^2*W^2:ℕ):ℝ) ≤ ((Q^2*bl*cl*(al+bl+cl)*(bl+cl-ah):ℕ):ℝ) := by exact_mod_cast hcheck
    push_cast [nat_sub_cast_max] at hh
    exact hh
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hbound : ((S:ℝ)*(W:ℝ)/(Q:ℝ))^2*((bh:ℝ)+(ch:ℝ))^2 ≤
      (bl:ℝ)*(cl:ℝ)*((al:ℝ)+(bl:ℝ)+(cl:ℝ))*max 0 ((bl:ℝ)+(cl:ℝ)-(ah:ℝ)) := by
    calc
      _ = ((S:ℝ)^2*((bh:ℝ)+(ch:ℝ))^2*(W:ℝ)^2)/(Q:ℝ)^2 := by ring
      _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hQr)).2 (by nlinarith only [hreal])
  exact bisector_interval_lower a b c al ah bl bh cl ch _ ha ha1 hb hb1 hc hc1
    (by positivity) (by positivity) (by positivity) htri hden hbound

theorem scaled_product_certificate (S Q R wa wb wc ma mb mc : ℕ)
    (hQ : 0 < Q)
    (h : Q^4*R^4 < 16*S^4*(wa+wb+wc)*(ma^3+mb^3+mc^3)) :
    ((R:ℝ)/2)^4 <
      ((S:ℝ)*(wa:ℝ)/(Q:ℝ)+(S:ℝ)*(wb:ℝ)/(Q:ℝ)+(S:ℝ)*(wc:ℝ)/(Q:ℝ))*
      (((S:ℝ)*(ma:ℝ)/(Q:ℝ))^3+((S:ℝ)*(mb:ℝ)/(Q:ℝ))^3+((S:ℝ)*(mc:ℝ)/(Q:ℝ))^3) := by
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hh : (Q:ℝ)^4*(R:ℝ)^4 < 16*(S:ℝ)^4*((wa:ℝ)+(wb:ℝ)+(wc:ℝ))*((ma:ℝ)^3+(mb:ℝ)^3+(mc:ℝ)^3) := by exact_mod_cast h
  have hd : (0:ℝ)<(Q:ℝ)^4 := pow_pos hQr _
  have result : (R:ℝ)^4/16 <
      ((S:ℝ)^4*((wa:ℝ)+(wb:ℝ)+(wc:ℝ))*((ma:ℝ)^3+(mb:ℝ)^3+(mc:ℝ)^3))/(Q:ℝ)^4 := by
    apply (lt_div_iff₀ hd).2
    nlinarith only [hh]
  convert result using 1 <;> ring

theorem certified_triangle_interval (a b : ℝ)
    (S Q al ah bl bh ma mb mc wa wb wc : ℕ)
    (hS : 0<S) (hQ : 0<Q)
    (ha : (al:ℝ) ≤ a) (ha1 : a ≤ (ah:ℝ))
    (hb : (bl:ℝ) ≤ b) (hb1 : b ≤ (bh:ℝ))
    (hab : a ≤ b) (hbS : b ≤ (S:ℝ)) (htri : (S:ℝ) ≤ a+b)
    (hma : 4*S^2*ma^2 ≤ Q^2*(2*bl^2+2*S^2-ah^2))
    (hmb : 4*S^2*mb^2 ≤ Q^2*(2*S^2+2*al^2-bh^2))
    (hmc : 4*S^2*mc^2 ≤ Q^2*(2*al^2+2*bl^2-S^2))
    (hwa : S^2*(bh+S)^2*wa^2 ≤ Q^2*bl*S*(al+bl+S)*(bl+S-ah))
    (hwb : S^2*(S+ah)^2*wb^2 ≤ Q^2*S*al*(bl+S+al)*(S+al-bh))
    (hwc : S^2*(ah+bh)^2*wc^2 ≤ Q^2*al*bl*(S+al+bl)*(al+bl-S))
    (hprod : Q^4*(ah+bh+S)^4 < 16*S^4*(wa+wb+wc)*(ma^3+mb^3+mc^3)) :
    ((a+b+(S:ℝ))/2)^4 <
      (bisector a b S+bisector b S a+bisector S a b)*
      ((median a b S)^3+(median b S a)^3+(median S a b)^3) := by
  have hSr : (0:ℝ)<S := by exact_mod_cast hS
  have ha0 : 0 ≤ a := le_trans (by positivity : (0:ℝ) ≤ al) ha
  have hb0 : 0 ≤ b := le_trans (by positivity : (0:ℝ) ≤ bl) hb
  have m1 := scaled_median_interval a b S S Q al ah bl bh S S ma hS hQ ha ha1 hb (le_refl _) hma
  have m2 := scaled_median_interval b S a S Q bl bh S S al ah mb hS hQ hb hb1 (le_refl _) ha hmb
  have m3 := scaled_median_interval S a b S Q S S al ah bl bh mc hS hQ (le_refl _) (le_refl _) ha hb hmc
  have w1 := scaled_bisector_interval a b S S Q al ah bl bh S S wa hQ ha ha1 hb hb1 (le_refl _) (le_refl _) (by linarith) (by linarith) hwa
  have w2 := scaled_bisector_interval b S a S Q bl bh S S al ah wb hQ hb hb1 (le_refl _) (le_refl _) ha ha1 (by linarith) (by linarith) hwb
  have w3 := scaled_bisector_interval S a b S Q S S al ah bl bh wc hQ (le_refl _) (le_refl _) ha ha1 hb hb1 (by linarith) (by linarith) hwc
  have hp := scaled_product_certificate S Q (ah+bh+S) wa wb wc ma mb mc hQ hprod
  have hup : ((a+b+(S:ℝ))/2)^4 ≤ (((ah+bh+S:ℕ):ℝ)/2)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  apply assemble_bounds _ _ _ _ _ _ _ _ _ _ _ _ _
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
    m1 m2 m3 w1 w2 w3
  exact lt_of_le_of_lt hup hp

#print axioms certified_triangle_interval
#print axioms scaled_product_certificate
#print axioms scaled_bisector_interval
#print axioms scaled_median_interval
#print axioms nat_sub_cast_max
#print axioms scaled_sqrt_bound
#print axioms local_triangle_inequality
#print axioms median_local_factor
#print axioms bisector_local_factor
#print axioms bisector_interval_lower
#print axioms local_radical_product
#print axioms aggregate_local_bounds
#print axioms median_interval_lower
#print axioms rational_radical_lower
#print axioms perturbation_bounds
#print axioms bisector_loss_bounds
#print axioms sqrt_lower
#print axioms sqrt_cube_lower
#print axioms local_product_bound
#print axioms assemble_bounds
#print axioms normalized_median_identity
#print axioms normalized_bisector_identity
end
end LiuReal
