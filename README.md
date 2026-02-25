# verus-linalg

Formally verified linear algebra primitives in Rust + Verus.

Generic vector types (`Vec2<T>`, `Vec3<T>`, `Vec4<T>`) over any `Ring`,
with verified algebraic properties (componentwise `AdditiveGroup`) and
proven operations (scale, dot, cross).

## Verification

Requires [Verus](https://github.com/verus-lang/verus) and
[verus-algebra](https://github.com/Phylliida/verus-algebra) checked out
as siblings:

```
VERUS_ROOT=../verus ./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 90
```
