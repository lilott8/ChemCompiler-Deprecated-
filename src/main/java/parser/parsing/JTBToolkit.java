package parser.parsing;

import parser.ast.NodeToken;

/**
 * @created: 1/30/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
class JTBToolkit {
    static NodeToken makeNodeToken(Token t) {
        return new NodeToken(t.image.intern(), t.kind, t.beginLine, t.beginColumn, t.endLine, t.endColumn);
    }
}
