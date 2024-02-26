# richelot_graph

　これは超特別アーベル曲面間の(2,2)-同種写像グラフ計算を、計算代数システムMagmaで実装したコードです。<br>
実行画面で
```
load "graph.m";
```
と入力すると、次のような連想配列`node_set`と配列`edge_set`が計算されます。
- `node_set`: キーは頂点のアーベル曲面に対応する不変量、要素はその頂点に割り振られた番号
- `edge_set`: キーは頂点に対応する番号、要素はその頂点から伸びる15本の辺が接続する頂点の番号
必要に応じて、ファイル"graph.m"内の3行目で標数を変更してください。
