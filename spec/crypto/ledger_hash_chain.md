# Ledger כ-Hash-Chain — מודל קריפטוגרפי

פונקציית גיבוב \( H:{0,1}^* \to {0,1}^k \).

בלוק: \( B_i = (\mathrm{data}_i, \mathrm{prev\_hash}_i, \mathrm{ts}_i) \), עם \( \mathrm{prev\_hash}_i = H(B_{i-1}) \).

יומן: \( L = \langle B_0,\ldots,B_n \rangle \), \(B_0\) ג׳נסיס.

**אינבריאנטים**
- **תקינות שרשרת:** \( B_i.\mathrm{prev\_hash} = H(B_{i-1}) \).
- **מחויבות זמן:** \( B_i.\mathrm{ts} > B_{i-1}.\mathrm{ts} \).

**השלכות**
- שינוי ב-\( \mathrm{data}_k \) שוברת את השרשרת החל מ-\(k\).
- מבטיח Replay עקבי על רצף הנתונים.
