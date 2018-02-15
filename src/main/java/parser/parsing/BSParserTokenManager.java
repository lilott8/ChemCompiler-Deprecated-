/* BSParserTokenManager.java */
/* Generated By:JavaCC: Do not edit this line. BSParserTokenManager.java */
package parser.parsing;
import parser.ast.*;
import java.util.Vector;

/** Token Manager. */
@SuppressWarnings("unused")public class BSParserTokenManager implements BSParserConstants {

  /** Debug output. */
  public  java.io.PrintStream debugStream = System.out;
  /** Set debug output. */
  public  void setDebugStream(java.io.PrintStream ds) { debugStream = ds; }
private final int jjStopStringLiteralDfa_0(int pos, long active0){
   switch (pos)
   {
      case 0:
         if ((active0 & 0x3800003fffffc0L) != 0L)
         {
            jjmatchedKind = 57;
            return 4;
         }
         return -1;
      case 1:
         if ((active0 & 0x3800003fdfb7c0L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 1;
            return 4;
         }
         if ((active0 & 0x204800L) != 0L)
            return 4;
         return -1;
      case 2:
         if ((active0 & 0x38000039dfb380L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 2;
            return 4;
         }
         if ((active0 & 0x6000440L) != 0L)
            return 4;
         return -1;
      case 3:
         if ((active0 & 0x10000001518200L) != 0L)
            return 4;
         if ((active0 & 0x280000388e3180L) != 0L)
         {
            if (jjmatchedPos != 3)
            {
               jjmatchedKind = 57;
               jjmatchedPos = 3;
            }
            return 4;
         }
         return -1;
      case 4:
         if ((active0 & 0x20000010080180L) != 0L)
            return 4;
         if ((active0 & 0x8000028863000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 4;
            return 4;
         }
         return -1;
      case 5:
         if ((active0 & 0x28003000L) != 0L)
            return 4;
         if ((active0 & 0x8000000860000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 5;
            return 4;
         }
         return -1;
      case 6:
         if ((active0 & 0x8000000860000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 6;
            return 4;
         }
         return -1;
      case 7:
         if ((active0 & 0x840000L) != 0L)
            return 4;
         if ((active0 & 0x8000000020000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 7;
            return 4;
         }
         return -1;
      case 8:
         if ((active0 & 0x8000000020000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 8;
            return 4;
         }
         return -1;
      case 9:
         if ((active0 & 0x20000L) != 0L)
            return 4;
         if ((active0 & 0x8000000000000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 9;
            return 4;
         }
         return -1;
      case 10:
         if ((active0 & 0x8000000000000L) != 0L)
         {
            jjmatchedKind = 57;
            jjmatchedPos = 10;
            return 4;
         }
         return -1;
      default :
         return -1;
   }
}
private final int jjStartNfa_0(int pos, long active0){
   return jjMoveNfa_0(jjStopStringLiteralDfa_0(pos, active0), pos + 1);
}
private int jjStopAtPos(int pos, int kind)
{
   jjmatchedKind = kind;
   jjmatchedPos = pos;
   return pos + 1;
}
private int jjMoveStringLiteralDfa0_0(){
   switch(curChar)
   {
      case 33:
         jjmatchedKind = 40;
         return jjMoveStringLiteralDfa1_0(0x20000000000L);
      case 38:
         return jjMoveStringLiteralDfa1_0(0x4000000000L);
      case 40:
         return jjStopAtPos(0, 30);
      case 41:
         return jjStopAtPos(0, 31);
      case 42:
         return jjStopAtPos(0, 49);
      case 43:
         return jjStopAtPos(0, 37);
      case 44:
         return jjStopAtPos(0, 54);
      case 45:
         return jjStopAtPos(0, 47);
      case 46:
         return jjStopAtPos(0, 36);
      case 47:
         return jjStopAtPos(0, 48);
      case 58:
         return jjStopAtPos(0, 55);
      case 60:
         jjmatchedKind = 42;
         return jjMoveStringLiteralDfa1_0(0x80000000000L);
      case 61:
         jjmatchedKind = 39;
         return jjMoveStringLiteralDfa1_0(0x400000000000L);
      case 62:
         jjmatchedKind = 44;
         return jjMoveStringLiteralDfa1_0(0x200000000000L);
      case 91:
         return jjStopAtPos(0, 32);
      case 93:
         return jjStopAtPos(0, 33);
      case 97:
         return jjMoveStringLiteralDfa1_0(0x10000800L);
      case 100:
         return jjMoveStringLiteralDfa1_0(0x1100L);
      case 101:
         return jjMoveStringLiteralDfa1_0(0x18000L);
      case 102:
         return jjMoveStringLiteralDfa1_0(0x20000000800400L);
      case 104:
         return jjMoveStringLiteralDfa1_0(0x200L);
      case 105:
         return jjMoveStringLiteralDfa1_0(0x8000000404000L);
      case 109:
         return jjMoveStringLiteralDfa1_0(0xc040040L);
      case 110:
         return jjMoveStringLiteralDfa1_0(0x2000000L);
      case 111:
         return jjMoveStringLiteralDfa1_0(0x200000L);
      case 114:
         return jjMoveStringLiteralDfa1_0(0x21002000L);
      case 115:
         return jjMoveStringLiteralDfa1_0(0x20080L);
      case 116:
         return jjMoveStringLiteralDfa1_0(0x10000000080000L);
      case 119:
         return jjMoveStringLiteralDfa1_0(0x100000L);
      case 123:
         return jjStopAtPos(0, 34);
      case 124:
         return jjMoveStringLiteralDfa1_0(0x4000000000000L);
      case 125:
         return jjStopAtPos(0, 35);
      default :
         return jjMoveNfa_0(0, 0);
   }
}
private int jjMoveStringLiteralDfa1_0(long active0){
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(0, active0);
      return 1;
   }
   switch(curChar)
   {
      case 38:
         if ((active0 & 0x4000000000L) != 0L)
            return jjStopAtPos(1, 38);
         break;
      case 61:
         if ((active0 & 0x20000000000L) != 0L)
            return jjStopAtPos(1, 41);
         else if ((active0 & 0x80000000000L) != 0L)
            return jjStopAtPos(1, 43);
         else if ((active0 & 0x200000000000L) != 0L)
            return jjStopAtPos(1, 45);
         else if ((active0 & 0x400000000000L) != 0L)
            return jjStopAtPos(1, 46);
         break;
      case 97:
         return jjMoveStringLiteralDfa2_0(active0, 0x20000006040000L);
      case 101:
         return jjMoveStringLiteralDfa2_0(active0, 0x21003200L);
      case 102:
         if ((active0 & 0x4000L) != 0L)
            return jjStartNfaWithStates_0(1, 14, 4);
         break;
      case 105:
         return jjMoveStringLiteralDfa2_0(active0, 0x180040L);
      case 108:
         return jjMoveStringLiteralDfa2_0(active0, 0x18000L);
      case 110:
         if ((active0 & 0x200000L) != 0L)
            return jjStartNfaWithStates_0(1, 21, 4);
         return jjMoveStringLiteralDfa2_0(active0, 0x8000000400000L);
      case 111:
         return jjMoveStringLiteralDfa2_0(active0, 0x8000400L);
      case 112:
         return jjMoveStringLiteralDfa2_0(active0, 0x80L);
      case 114:
         return jjMoveStringLiteralDfa2_0(active0, 0x10000010000100L);
      case 116:
         if ((active0 & 0x800L) != 0L)
            return jjStartNfaWithStates_0(1, 11, 4);
         return jjMoveStringLiteralDfa2_0(active0, 0x20000L);
      case 117:
         return jjMoveStringLiteralDfa2_0(active0, 0x800000L);
      case 124:
         if ((active0 & 0x4000000000000L) != 0L)
            return jjStopAtPos(1, 50);
         break;
      default :
         break;
   }
   return jjStartNfa_0(0, active0);
}
private int jjMoveStringLiteralDfa2_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(0, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(1, active0);
      return 2;
   }
   switch(curChar)
   {
      case 97:
         return jjMoveStringLiteralDfa3_0(active0, 0x1020300L);
      case 100:
         return jjMoveStringLiteralDfa3_0(active0, 0x8000000L);
      case 108:
         return jjMoveStringLiteralDfa3_0(active0, 0x20000000000080L);
      case 109:
         return jjMoveStringLiteralDfa3_0(active0, 0x80000L);
      case 110:
         return jjMoveStringLiteralDfa3_0(active0, 0x840000L);
      case 112:
         return jjMoveStringLiteralDfa3_0(active0, 0x2000L);
      case 114:
         if ((active0 & 0x400L) != 0L)
            return jjStartNfaWithStates_0(2, 10, 4);
         return jjMoveStringLiteralDfa3_0(active0, 0x10000000L);
      case 115:
         return jjMoveStringLiteralDfa3_0(active0, 0x8000000018000L);
      case 116:
         if ((active0 & 0x2000000L) != 0L)
            return jjStartNfaWithStates_0(2, 25, 4);
         else if ((active0 & 0x4000000L) != 0L)
            return jjStartNfaWithStates_0(2, 26, 4);
         return jjMoveStringLiteralDfa3_0(active0, 0x20501000L);
      case 117:
         return jjMoveStringLiteralDfa3_0(active0, 0x10000000000000L);
      case 120:
         if ((active0 & 0x40L) != 0L)
            return jjStartNfaWithStates_0(2, 6, 4);
         break;
      default :
         break;
   }
   return jjStartNfa_0(1, active0);
}
private int jjMoveStringLiteralDfa3_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(1, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(2, active0);
      return 3;
   }
   switch(curChar)
   {
      case 97:
         return jjMoveStringLiteralDfa4_0(active0, 0x10000000L);
      case 99:
         return jjMoveStringLiteralDfa4_0(active0, 0x800000L);
      case 101:
         if ((active0 & 0x10000L) != 0L)
         {
            jjmatchedKind = 16;
            jjmatchedPos = 3;
         }
         else if ((active0 & 0x10000000000000L) != 0L)
            return jjStartNfaWithStates_0(3, 52, 4);
         return jjMoveStringLiteralDfa4_0(active0, 0x8b000L);
      case 104:
         if ((active0 & 0x100000L) != 0L)
            return jjStartNfaWithStates_0(3, 20, 4);
         break;
      case 105:
         return jjMoveStringLiteralDfa4_0(active0, 0x40180L);
      case 108:
         if ((active0 & 0x1000000L) != 0L)
            return jjStartNfaWithStates_0(3, 24, 4);
         break;
      case 111:
         if ((active0 & 0x400000L) != 0L)
            return jjStartNfaWithStates_0(3, 22, 4);
         break;
      case 115:
         return jjMoveStringLiteralDfa4_0(active0, 0x20000000000000L);
      case 116:
         if ((active0 & 0x200L) != 0L)
            return jjStartNfaWithStates_0(3, 9, 4);
         return jjMoveStringLiteralDfa4_0(active0, 0x8000000020000L);
      case 117:
         return jjMoveStringLiteralDfa4_0(active0, 0x28000000L);
      default :
         break;
   }
   return jjStartNfa_0(2, active0);
}
private int jjMoveStringLiteralDfa4_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(2, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(3, active0);
      return 4;
   }
   switch(curChar)
   {
      case 32:
         return jjMoveStringLiteralDfa5_0(active0, 0x8000L);
      case 97:
         return jjMoveStringLiteralDfa5_0(active0, 0x2000L);
      case 99:
         return jjMoveStringLiteralDfa5_0(active0, 0x1000L);
      case 101:
         if ((active0 & 0x20000000000000L) != 0L)
            return jjStartNfaWithStates_0(4, 53, 4);
         break;
      case 102:
         return jjMoveStringLiteralDfa5_0(active0, 0x40000L);
      case 105:
         return jjMoveStringLiteralDfa5_0(active0, 0x20000L);
      case 108:
         return jjMoveStringLiteralDfa5_0(active0, 0x8000000L);
      case 110:
         if ((active0 & 0x100L) != 0L)
            return jjStartNfaWithStates_0(4, 8, 4);
         break;
      case 114:
         return jjMoveStringLiteralDfa5_0(active0, 0x8000020000000L);
      case 115:
         if ((active0 & 0x80000L) != 0L)
            return jjStartNfaWithStates_0(4, 19, 4);
         break;
      case 116:
         if ((active0 & 0x80L) != 0L)
            return jjStartNfaWithStates_0(4, 7, 4);
         return jjMoveStringLiteralDfa5_0(active0, 0x800000L);
      case 121:
         if ((active0 & 0x10000000L) != 0L)
            return jjStartNfaWithStates_0(4, 28, 4);
         break;
      default :
         break;
   }
   return jjStartNfa_0(3, active0);
}
private int jjMoveStringLiteralDfa5_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(3, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(4, active0);
      return 5;
   }
   switch(curChar)
   {
      case 101:
         if ((active0 & 0x8000000L) != 0L)
            return jjStartNfaWithStates_0(5, 27, 4);
         return jjMoveStringLiteralDfa6_0(active0, 0x40000L);
      case 105:
         return jjMoveStringLiteralDfa6_0(active0, 0x808000L);
      case 110:
         if ((active0 & 0x20000000L) != 0L)
            return jjStartNfaWithStates_0(5, 29, 4);
         break;
      case 111:
         return jjMoveStringLiteralDfa6_0(active0, 0x20000L);
      case 116:
         if ((active0 & 0x1000L) != 0L)
            return jjStartNfaWithStates_0(5, 12, 4);
         else if ((active0 & 0x2000L) != 0L)
            return jjStartNfaWithStates_0(5, 13, 4);
         break;
      case 117:
         return jjMoveStringLiteralDfa6_0(active0, 0x8000000000000L);
      default :
         break;
   }
   return jjStartNfa_0(4, active0);
}
private int jjMoveStringLiteralDfa6_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(4, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(5, active0);
      return 6;
   }
   switch(curChar)
   {
      case 99:
         return jjMoveStringLiteralDfa7_0(active0, 0x8000000000000L);
      case 102:
         if ((active0 & 0x8000L) != 0L)
            return jjStopAtPos(6, 15);
         break;
      case 110:
         return jjMoveStringLiteralDfa7_0(active0, 0x20000L);
      case 111:
         return jjMoveStringLiteralDfa7_0(active0, 0x800000L);
      case 115:
         return jjMoveStringLiteralDfa7_0(active0, 0x40000L);
      default :
         break;
   }
   return jjStartNfa_0(5, active0);
}
private int jjMoveStringLiteralDfa7_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(5, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(6, active0);
      return 7;
   }
   switch(curChar)
   {
      case 97:
         return jjMoveStringLiteralDfa8_0(active0, 0x20000L);
      case 110:
         if ((active0 & 0x800000L) != 0L)
            return jjStartNfaWithStates_0(7, 23, 4);
         break;
      case 116:
         if ((active0 & 0x40000L) != 0L)
            return jjStartNfaWithStates_0(7, 18, 4);
         return jjMoveStringLiteralDfa8_0(active0, 0x8000000000000L);
      default :
         break;
   }
   return jjStartNfa_0(6, active0);
}
private int jjMoveStringLiteralDfa8_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(6, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(7, active0);
      return 8;
   }
   switch(curChar)
   {
      case 105:
         return jjMoveStringLiteralDfa9_0(active0, 0x8000000000000L);
      case 114:
         return jjMoveStringLiteralDfa9_0(active0, 0x20000L);
      default :
         break;
   }
   return jjStartNfa_0(7, active0);
}
private int jjMoveStringLiteralDfa9_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(7, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(8, active0);
      return 9;
   }
   switch(curChar)
   {
      case 111:
         return jjMoveStringLiteralDfa10_0(active0, 0x8000000000000L);
      case 121:
         if ((active0 & 0x20000L) != 0L)
            return jjStartNfaWithStates_0(9, 17, 4);
         break;
      default :
         break;
   }
   return jjStartNfa_0(8, active0);
}
private int jjMoveStringLiteralDfa10_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(8, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(9, active0);
      return 10;
   }
   switch(curChar)
   {
      case 110:
         return jjMoveStringLiteralDfa11_0(active0, 0x8000000000000L);
      default :
         break;
   }
   return jjStartNfa_0(9, active0);
}
private int jjMoveStringLiteralDfa11_0(long old0, long active0){
   if (((active0 &= old0)) == 0L)
      return jjStartNfa_0(9, old0);
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) {
      jjStopStringLiteralDfa_0(10, active0);
      return 11;
   }
   switch(curChar)
   {
      case 115:
         if ((active0 & 0x8000000000000L) != 0L)
            return jjStartNfaWithStates_0(11, 51, 4);
         break;
      default :
         break;
   }
   return jjStartNfa_0(10, active0);
}
private int jjStartNfaWithStates_0(int pos, int kind, int state)
{
   jjmatchedKind = kind;
   jjmatchedPos = pos;
   try { curChar = input_stream.readChar(); }
   catch(java.io.IOException e) { return pos + 1; }
   return jjMoveNfa_0(state, pos + 1);
}
static final long[] jjbitVec0 = {
   0x1ff00000fffffffeL, 0xffffffffffffc000L, 0xffffffffL, 0x600000000000000L
};
static final long[] jjbitVec2 = {
   0x0L, 0x0L, 0x0L, 0xff7fffffff7fffffL
};
static final long[] jjbitVec3 = {
   0x0L, 0xffffffffffffffffL, 0xffffffffffffffffL, 0xffffffffffffffffL
};
static final long[] jjbitVec4 = {
   0xffffffffffffffffL, 0xffffffffffffffffL, 0xffffL, 0x0L
};
static final long[] jjbitVec5 = {
   0xffffffffffffffffL, 0xffffffffffffffffL, 0x0L, 0x0L
};
static final long[] jjbitVec6 = {
   0x3fffffffffffL, 0x0L, 0x0L, 0x0L
};
private int jjMoveNfa_0(int startState, int curPos)
{
   int startsAt = 0;
   jjnewStateCnt = 5;
   int i = 1;
   jjstateSet[0] = startState;
   int kind = 0x7fffffff;
   for (;;)
   {
      if (++jjround == 0x7fffffff)
         ReInitRounds();
      if (curChar < 64)
      {
         long l = 1L << curChar;
         do
         {
            switch(jjstateSet[--i])
            {
               case 0:
                  if ((0x3fe000000000000L & l) != 0L)
                  {
                     if (kind > 56)
                        kind = 56;
                     { jjCheckNAdd(1); }
                  }
                  else if (curChar == 36)
                  {
                     if (kind > 57)
                        kind = 57;
                     { jjCheckNAdd(4); }
                  }
                  else if (curChar == 48)
                  {
                     if (kind > 56)
                        kind = 56;
                  }
                  break;
               case 1:
                  if ((0x3ff000000000000L & l) == 0L)
                     break;
                  if (kind > 56)
                     kind = 56;
                  { jjCheckNAdd(1); }
                  break;
               case 2:
                  if (curChar == 48 && kind > 56)
                     kind = 56;
                  break;
               case 3:
                  if (curChar != 36)
                     break;
                  if (kind > 57)
                     kind = 57;
                  { jjCheckNAdd(4); }
                  break;
               case 4:
                  if ((0x3ff001000000000L & l) == 0L)
                     break;
                  if (kind > 57)
                     kind = 57;
                  { jjCheckNAdd(4); }
                  break;
               default : break;
            }
         } while(i != startsAt);
      }
      else if (curChar < 128)
      {
         long l = 1L << (curChar & 077);
         do
         {
            switch(jjstateSet[--i])
            {
               case 0:
               case 4:
                  if ((0x7fffffe87fffffeL & l) == 0L)
                     break;
                  if (kind > 57)
                     kind = 57;
                  { jjCheckNAdd(4); }
                  break;
               default : break;
            }
         } while(i != startsAt);
      }
      else
      {
         int hiByte = (curChar >> 8);
         int i1 = hiByte >> 6;
         long l1 = 1L << (hiByte & 077);
         int i2 = (curChar & 0xff) >> 6;
         long l2 = 1L << (curChar & 077);
         do
         {
            switch(jjstateSet[--i])
            {
               case 0:
               case 4:
                  if (!jjCanMove_0(hiByte, i1, i2, l1, l2))
                     break;
                  if (kind > 57)
                     kind = 57;
                  { jjCheckNAdd(4); }
                  break;
               default : if (i1 == 0 || l1 == 0 || i2 == 0 ||  l2 == 0) break; else break;
            }
         } while(i != startsAt);
      }
      if (kind != 0x7fffffff)
      {
         jjmatchedKind = kind;
         jjmatchedPos = curPos;
         kind = 0x7fffffff;
      }
      ++curPos;
      if ((i = jjnewStateCnt) == (startsAt = 5 - (jjnewStateCnt = startsAt)))
         return curPos;
      try { curChar = input_stream.readChar(); }
      catch(java.io.IOException e) { return curPos; }
   }
}
static final int[] jjnextStates = {
};
private static final boolean jjCanMove_0(int hiByte, int i1, int i2, long l1, long l2)
{
   switch(hiByte)
   {
      case 0:
         return ((jjbitVec2[i2] & l2) != 0L);
      case 48:
         return ((jjbitVec3[i2] & l2) != 0L);
      case 49:
         return ((jjbitVec4[i2] & l2) != 0L);
      case 51:
         return ((jjbitVec5[i2] & l2) != 0L);
      case 61:
         return ((jjbitVec6[i2] & l2) != 0L);
      default :
         if ((jjbitVec0[i1] & l1) != 0L)
            return true;
         return false;
   }
}

/** Token literal values. */
public static final String[] jjstrLiteralImages = {
"", null, null, null, null, null, "\155\151\170", "\163\160\154\151\164",
"\144\162\141\151\156", "\150\145\141\164", "\146\157\162", "\141\164", "\144\145\164\145\143\164",
"\162\145\160\145\141\164", "\151\146", "\145\154\163\145\40\151\146", "\145\154\163\145",
"\163\164\141\164\151\157\156\141\162\171", "\155\141\156\151\146\145\163\164", "\164\151\155\145\163",
"\167\151\164\150", "\157\156", "\151\156\164\157", "\146\165\156\143\164\151\157\156",
"\162\145\141\154", "\156\141\164", "\155\141\164", "\155\157\144\165\154\145",
"\141\162\162\141\171", "\162\145\164\165\162\156", "\50", "\51", "\133", "\135", "\173", "\175",
"\56", "\53", "\46\46", "\75", "\41", "\41\75", "\74", "\74\75", "\76", "\76\75",
"\75\75", "\55", "\57", "\52", "\174\174",
"\151\156\163\164\162\165\143\164\151\157\156\163", "\164\162\165\145", "\146\141\154\163\145", "\54", "\72", null, null, null,
null, };
protected Token jjFillToken()
{
   final Token t;
   final String curTokenImage;
   final int beginLine;
   final int endLine;
   final int beginColumn;
   final int endColumn;
   String im = jjstrLiteralImages[jjmatchedKind];
   curTokenImage = (im == null) ? input_stream.GetImage() : im;
   beginLine = input_stream.getBeginLine();
   beginColumn = input_stream.getBeginColumn();
   endLine = input_stream.getEndLine();
   endColumn = input_stream.getEndColumn();
   t = Token.newToken(jjmatchedKind, curTokenImage);

   t.beginLine = beginLine;
   t.endLine = endLine;
   t.beginColumn = beginColumn;
   t.endColumn = endColumn;

   return t;
}

int curLexState = 0;
int defaultLexState = 0;
int jjnewStateCnt;
int jjround;
int jjmatchedPos;
int jjmatchedKind;

/** Get the next Token. */
public Token getNextToken()
{
  Token matchedToken;
  int curPos = 0;

  EOFLoop :
  for (;;)
  {
   try
   {
      curChar = input_stream.BeginToken();
   }
   catch(java.io.IOException e)
   {
      jjmatchedKind = 0;
      jjmatchedPos = -1;
      matchedToken = jjFillToken();
      return matchedToken;
   }

   try { input_stream.backup(0);
      while (curChar <= 32 && (0x100003600L & (1L << curChar)) != 0L)
         curChar = input_stream.BeginToken();
   }
   catch (java.io.IOException e1) { continue EOFLoop; }
   jjmatchedKind = 0x7fffffff;
   jjmatchedPos = 0;
   curPos = jjMoveStringLiteralDfa0_0();
   if (jjmatchedKind != 0x7fffffff)
   {
      if (jjmatchedPos + 1 < curPos)
         input_stream.backup(curPos - jjmatchedPos - 1);
      if ((jjtoToken[jjmatchedKind >> 6] & (1L << (jjmatchedKind & 077))) != 0L)
      {
         matchedToken = jjFillToken();
         return matchedToken;
      }
      else
      {
         continue EOFLoop;
      }
   }
   int error_line = input_stream.getEndLine();
   int error_column = input_stream.getEndColumn();
   String error_after = null;
   boolean EOFSeen = false;
   try { input_stream.readChar(); input_stream.backup(1); }
   catch (java.io.IOException e1) {
      EOFSeen = true;
      error_after = curPos <= 1 ? "" : input_stream.GetImage();
      if (curChar == '\n' || curChar == '\r') {
         error_line++;
         error_column = 0;
      }
      else
         error_column++;
   }
   if (!EOFSeen) {
      input_stream.backup(1);
      error_after = curPos <= 1 ? "" : input_stream.GetImage();
   }
   throw new TokenMgrError(EOFSeen, curLexState, error_line, error_column, error_after, curChar, TokenMgrError.LEXICAL_ERROR);
  }
}

private void jjCheckNAdd(int state)
{
   if (jjrounds[state] != jjround)
   {
      jjstateSet[jjnewStateCnt++] = state;
      jjrounds[state] = jjround;
   }
}
private void jjAddStates(int start, int end)
{
   do {
      jjstateSet[jjnewStateCnt++] = jjnextStates[start];
   } while (start++ != end);
}
private void jjCheckNAddTwoStates(int state1, int state2)
{
   jjCheckNAdd(state1);
   jjCheckNAdd(state2);
}

    /** Constructor. */
    public BSParserTokenManager(JavaCharStream stream){

      if (JavaCharStream.staticFlag)
            throw new Error("ERROR: Cannot use a static CharStream class with a non-static lexical analyzer.");

    input_stream = stream;
  }

  /** Constructor. */
  public BSParserTokenManager (JavaCharStream stream, int lexState){
    ReInit(stream);
    SwitchTo(lexState);
  }

  /** Reinitialise parser. */
  public void ReInit(JavaCharStream stream)
  {
    jjmatchedPos = jjnewStateCnt = 0;
    curLexState = defaultLexState;
    input_stream = stream;
    ReInitRounds();
  }

  private void ReInitRounds()
  {
    int i;
    jjround = 0x80000001;
    for (i = 5; i-- > 0;)
      jjrounds[i] = 0x80000000;
  }

  /** Reinitialise parser. */
  public void ReInit(JavaCharStream stream, int lexState)
  {
    ReInit(stream);
    SwitchTo(lexState);
  }

  /** Switch to specified lex state. */
  public void SwitchTo(int lexState)
  {
    if (lexState >= 1 || lexState < 0)
      throw new TokenMgrError("Error: Ignoring invalid lexical state : " + lexState + ". State unchanged.", TokenMgrError.INVALID_LEXICAL_STATE);
    else
      curLexState = lexState;
  }

/** Lexer state names. */
public static final String[] lexStateNames = {
   "DEFAULT",
};
static final long[] jjtoToken = {
   0x3ffffffffffffc1L,
};
static final long[] jjtoSkip = {
   0x3eL,
};
    protected JavaCharStream  input_stream;

    private final int[] jjrounds = new int[5];
    private final int[] jjstateSet = new int[2 * 5];


    protected char curChar;
}
