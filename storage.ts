import { db } from "./db";
import { botStatus, trades, candidates } from "@shared/schema";
import { eq, desc, and, sql } from "drizzle-orm";

export interface IStorage {
  getBotStatus(): Promise<any>;
  getTrades(): Promise<any[]>;
  getOpenTrades(): Promise<any[]>;
  getCandidates(): Promise<any[]>;
  addTrade(trade: any): Promise<any>;
  closeTrade(id: number, exitPrice: string, pnl: string, exitReason?: string): Promise<void>;
  updateTradeCurrentPrice(id: number, currentPrice: string, pnl: string): Promise<void>;
  updateTradePeakPrice(id: number, peakPrice: string, peakPnl: string): Promise<void>;
  updateTradeAmount(id: number, amount: string): Promise<void>;
  updateTradingMode(mode: string): Promise<any>;
  updateBotRunning(isRunning: boolean): Promise<any>;
  updateStrategyMode(mode: string): Promise<any>;
  updateBotStats(stats: { walletBalance?: string; totalPnl?: string; winRate?: string; totalTrades?: number; openPositions?: number; lastSignal?: string; peakBalance?: string; dailyStartBalance?: string; lastLossCooldownEnd?: number }): Promise<void>;
  seedInitialData(): Promise<void>;
}

export class DatabaseStorage implements IStorage {
  async getBotStatus(): Promise<any> {
    const status = await db.select().from(botStatus).limit(1);
    return status[0] || { mode: "STOPPED", tradingMode: "paper", isRunning: false, walletBalance: "0", totalPnl: "0", winRate: "0", totalTrades: 0, openPositions: 0, lastSignal: null };
  }

  async getTrades(): Promise<any[]> {
    return await db.select().from(trades).orderBy(desc(trades.timestamp)).limit(100);
  }

  async getOpenTrades(): Promise<any[]> {
    return await db.select().from(trades).where(eq(trades.status, "OPEN")).orderBy(desc(trades.timestamp));
  }

  async getCandidates(): Promise<any[]> {
    return await db.select().from(candidates).orderBy(desc(candidates.timestamp)).limit(50);
  }

  async addTrade(trade: any): Promise<any> {
    // Always override timestamp with an explicit Date object.
    // Pass new Date() (not new Date().toISOString()) — Drizzle's PgTimestamp
    // column calls .toISOString() internally on the value it receives. Passing
    // a string causes "value.toISOString is not a function" at runtime because
    // strings do not have that method. Using a Date object also avoids locale-
    // formatted strings from the DB default (e.g. "3/30/2026, 1:40 AM") which
    // would make IST timestamps appear ~5.5h in the future, causing negative
    // tradeAgeMs and permanently suppressing the desync grace-period exit.
    const [inserted] = await db.insert(trades).values({
      ...trade,
      timestamp: new Date(),
    }).returning();
    return inserted;
  }

  async closeTrade(id: number, exitPrice: string, pnl: string, exitReason?: string): Promise<void> {
    await db.update(trades).set({
      status: "CLOSED",
      type: "SELL",
      exitPrice,
      pnl,
      exitReason: exitReason || "MANUAL",
      closedAt: new Date(),
    }).where(eq(trades.id, id));
  }

  async updateTradeCurrentPrice(id: number, currentPrice: string, pnl: string): Promise<void> {
    await db.update(trades).set({ currentPrice, pnl }).where(eq(trades.id, id));
  }

  async updateTradePeakPrice(id: number, peakPrice: string, peakPnl: string): Promise<void> {
    await db.update(trades).set({ peakPrice, peakPnl }).where(eq(trades.id, id));
  }

  async updateTradeAmount(id: number, amount: string): Promise<void> {
    await db.update(trades).set({ amount }).where(eq(trades.id, id));
  }

  async updateTradingMode(mode: string): Promise<any> {
    const existing = await db.select().from(botStatus).limit(1);
    if (existing.length > 0) {
      await db.update(botStatus).set({ tradingMode: mode, lastUpdate: new Date() }).where(eq(botStatus.id, existing[0].id));
    }
    return this.getBotStatus();
  }

  async updateBotRunning(isRunning: boolean): Promise<any> {
    const existing = await db.select().from(botStatus).limit(1);
    if (existing.length > 0) {
      await db.update(botStatus).set({ isRunning, lastUpdate: new Date() }).where(eq(botStatus.id, existing[0].id));
    }
    return this.getBotStatus();
  }

  async updateStrategyMode(mode: string): Promise<any> {
    const existing = await db.select().from(botStatus).limit(1);
    if (existing.length > 0) {
      await db.update(botStatus).set({ mode, lastUpdate: new Date() }).where(eq(botStatus.id, existing[0].id));
    }
    return this.getBotStatus();
  }

  async updateBotStats(stats: { walletBalance?: string; totalPnl?: string; winRate?: string; totalTrades?: number; openPositions?: number; lastSignal?: string; peakBalance?: string; dailyStartBalance?: string; lastLossCooldownEnd?: number }): Promise<void> {
    const existing = await db.select().from(botStatus).limit(1);
    if (existing.length > 0) {
      await db.update(botStatus).set({ ...stats, lastUpdate: new Date() }).where(eq(botStatus.id, existing[0].id));
    }
  }

  async seedInitialData(): Promise<void> {
    const existingStatus = await db.select().from(botStatus).limit(1);
    if (existingStatus.length === 0) {
      await db.insert(botStatus).values({
        mode: "AUTO",
        tradingMode: "paper",
        isRunning: true,
        walletBalance: "10.00",
        totalPnl: "0",
        winRate: "0",
        totalTrades: 0,
        openPositions: 0,
      });
    }
  }
}

export const storage = new DatabaseStorage();
