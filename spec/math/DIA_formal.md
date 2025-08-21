# DIA — הגדרות פורמליות ומונוטוניות

## DIA_graph (קישוריות)
מודל: גרף מכוון \(G=(V,E)\) של קשרים סיבתיים.  
הגדרה: \[ \mathrm{DIA}_{\text{graph}}(G) := \frac{|E|}{|V|\cdot(|V|-1)} \]  
טווח: 0..1 (צפיפות).

## DIA_info (תוכן מידע)
לכל אירוע \(e\) סט תכונות \(A(e)\).  
\[ \mathrm{DIA}_{\text{info}}(e) := -\sum_{a_i \in A(e)} p(a_i)\log_2 p(a_i) \]  
(הערכה אמפירית של \(p\)).

## DIA_replay (יכולת שחזור)
Ledger \(L=\langle e_1,\ldots,e_n\rangle\); מעבר מצב דטרמיניסטי \(f\).  
\( \mathrm{DIA}_{\text{replay}}(L)=\text{TRUE} \) אם \( s_k = f(\cdots f(f(s_0,e_1),e_2)\cdots,e_k) \) מוגדר היטב לכל \(k\).

## מונוטוניות
הגדרה שמרנית: \[ \mathrm{DIA}(s_{j}) \ge \mathrm{DIA}(s_{i}) \quad \text{לכל מעבר חוקי } s_i\to s_j. \]
ניתן לבחור \( \mathrm{DIA} \) כצירוף משוקלל של שלושת המדדים; בברירת מחדל: אי-ירידה מוחלטת (\(\tau=0\)).
