# Generative Entropy Utilities

The generative helpers provide simple primitives for experimenting with
concept generation in Φ‑OS.  They are primarily intended for prototypes
and research.

## Usage

```python
from generative.protocol import generate
from generative.entropy_tools import normalised_entropy

result = generate(["alpha", "beta"], per_seed=2, rng_seed=42)
print(result.concepts)
print(result.entropy)
print(result.normalised_entropy)
```

`normalised_entropy` scales scores by the theoretical maximum for the
number of distinct concepts.  This makes comparisons across different
sample sizes meaningful and helps when tuning entropy thresholds.

## Tuning

* **Thresholds** – Higher thresholds favour more diverse concept sets.
  Values around `0.7`–`0.9` typically indicate good spread while `1.0`
  means a perfectly uniform distribution.
* **Seeds** – Add more seed tags to broaden the search space and increase
  entropy.  Reusing the same random seed keeps experiments reproducible.

## Integration

Generated concept distributions can be analysed alongside other Φ‑OS
modules.  For example, the resulting entropy score may be combined with
`sim_replay.dia_info` to prioritise high‑diversity event streams.
