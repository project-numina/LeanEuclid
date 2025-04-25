import SystemE.Theory.Sorts
import SystemE.Theory.Relations
import SystemE.Tactic.Attr

--
-- Metric inferences defined in Sec. 3.5 of Avigad et al., 2009
-- Generally speaking, they are not used explicitly in the tactics written by humans.
-- *
--   + is associative and commutative, with identity 0.

--   < is a linear ordering with least element 0

--   For any x, y, and z, if x < y then x + z < y + z

--
-- 1.
-- ab = 0 if and only if a = b.
--



@[euclid]
axiom zero_segment_if :
  ∀ (a b : Point),  |(a ─ b)| = 0 → a = b


@[euclid]
axiom zero_segment_onlyif : ∀ (a b : Point),
  a = b → |(a─b)| = 0

-- --
-- 2.
-- ab ≥ 0
--
@[simp]
axiom segment_gte_zero : ∀ (s : Segment),
  0 ≤ s.length

--
-- 3.
-- ab = ba.
--
-- @[simp]
@[euclid]
axiom segment_symmetric : ∀ (a b : Point),
  |(a─b)| = |(b─a)|
--


@[euclid]
axiom angle_symm : ∀ (a b c : Point),
  (a ≠ b) ∧ (b ≠ c) → ((∠ a:b:c) = (∠ c:b:a))

--
-- 5.
-- 0 ≤ \abc and \abc ≤ right-angle + right-angle.
-- --
-- @[simp]
@[euclid]
axiom angle_range : ∀ (ang : Angle),
  (0 : ℝ) ≤ ang ∧ ang ≤ ∟ + ∟

--
-- 6.
-- △aab = 0. △
--
-- @[simp]
@[euclid]
axiom degenerated_area : ∀ (a b : Point), Triangle.area △ a:a:b = 0

--
-- 7.
-- △abc ≥ 0.
-- --
-- @[simp]
@[euclid]
axiom area_gte_zero : ∀ (ar : Triangle), 0 ≤ Triangle.area ar

--
-- 8.
-- △abc = △cab and △abc = △acb.
--
-- @[simp]
@[euclid]
axiom area_symm_1 : ∀ (a b c : Point),
    Triangle.area (△a:b:c) = Triangle.area (△c:a:b)

-- @[simp]
@[euclid]
axiom area_symm_2 : ∀ (a b c : Point),
    Triangle.area (△ a:b:c) = Triangle.area (△a:c:b)

--
-- 9.
-- If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
-- \cab = \c′a′b′, then △abc = △a′b′c′.
--

@[euclid]
axiom area_congruence : ∀ (a b c a' b' c' : Point),
    |(a─b)| = |(a'─b')| ∧
    |(b─c)| = |(b'─c')| ∧
    |(c─a)| = |(c'─a')| ∧
    ∠ a:b:c = ∠ a':b':c' ∧
    ∠ b:c:a = ∠ b':c':a' ∧
    ∠ c:a:b = ∠ c':a':b'
    → Triangle.area (△ a:b:c) = Triangle.area (△ a':b':c')
