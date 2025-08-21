# OpenDecision-SSM — מודל סטטיסטי פורמלי

השערות \(H_1,\ldots,H_m\) עם p-values \(p_1,\ldots,p_m\).

- **FWER:** \( \mathrm{FWER} = P(V \ge 1) \).
- **FDR:** \( \mathrm{FDR} = \mathbb{E}\left[ \frac{V}{\max(R,1)} \right] \).

פסאודו-קוד (עם בדיקת DIA):

```
FUNCTION OpenDecision(p_values, risk_level, alpha):
    m = length(p_values)
    sorted_p = sort_with_indices(p_values)

    IF DIA_check() == FALSE:
        RETURN "Early-Stop: DIA violation"

    IF risk_level == "Critical":
        // Holm-Bonferroni
        FOR k FROM 1 TO m:
            p_k = sorted_p[k].value
            IF p_k > alpha / (m - k + 1):
                RETURN reject(sorted_p, k - 1)
        RETURN reject(sorted_p, m)

    ELSE:
        // Benjamini–Hochberg
        k_max = 0
        FOR k FROM m DOWNTO 1:
            p_k = sorted_p[k].value
            IF p_k <= (k / m) * alpha:
                k_max = k
                BREAK
        RETURN reject(sorted_p, k_max)
```
