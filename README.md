# jsp-000728-maximal-sum-free

## English

- **JSP id:** JSP-000728
- **Title:** How many inclusion-maximal sum-free subsets does a finite integer interval have?
- **Catalog:** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000728
- **Status:** WIP / PARTIAL — harness may be green on weaker lemmas, but the **full catalog statement is not yet formalized**.
- **Prize claim:** **NOT claiming** the Justin Sun Prize yet.
- **Owner:** [Yi-111-a](https://github.com/Yi-111-a) (public Lean repo for a future claim must be owned by this account).

### Prize rules reminder

Only a **complete** Lean formalization of the **original** catalog problem is eligible.
Partial mathematics or incomplete Lean (`sorry`/`admit`, unproved assumptions) is not eligible.
Do not put Lean sources into `TheJustinSunPrize/awards`; catalog PRs should link out only.
Pin a full 40-character commit SHA when claiming later.

### Build

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd lean
lake build
```

See `lean/lean-toolchain` for the pinned toolchain. See `ACCEPTANCE.md` for the prize gate and required headline theorem name(s).

## 中文

- **题目编号：** JSP-000728
- **标题：** 有限整数区间有多少个包含极大无和无子集？
- **目录条目：** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000728
- **状态：** 进行中 / **部分结果** — harness 在较弱引理上可能已通过，但**完整原题陈述尚未形式化**。
- **领奖：** **尚未**就 Justin Sun Prize 提出 claim。
- **仓库所有者：** Yi-111-a（未来 claim 的公开 Lean 仓库必须由该账号拥有）。

### 规则提醒

仅接受对**原题完整陈述**的**完整** Lean 形式化；部分数学或含 `sorry`/`admit` 的不完整形式化不具备资格。
不要把 Lean 源码放进 awards 仓库；目录 PR 只放链接。claim 时需钉死完整 40 位 commit SHA。

### 构建

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd lean
lake build
```
