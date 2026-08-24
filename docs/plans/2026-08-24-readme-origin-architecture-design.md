# README 来源与架构设计

README 分三部分介绍项目：Cordis 论文及其 DeepSeek Harness 背景、Cordis 的
简要概念架构，以及本 Lean 机制化的范围与结果。文字必须保留项目的形式化
边界：这里只验证 Cordis 部分思想的简化模型，而非完整论文、DeepSeek
Harness 或实际实现。

架构概览说明 fiber、provider 与 consumer、committed/target dependency view、
生命周期 normalization、可逆 effects 和 quiet-only provider replacement，并
使用紧凑文本图展示它们的关系。现有分层、构建、审计和建模内容在此背景下
重新组织并保留。
