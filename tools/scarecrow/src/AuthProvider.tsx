import {
  createContext,
  PropsWithChildren,
  useCallback,
  useContext,
  useEffect,
  useState,
} from "react";

export interface AuthContext {
  isAuthenticated: boolean;
  login: (token: string) => Promise<void>;
  logout: () => Promise<void>;
  token: string | null;
}

const AuthContext = createContext<AuthContext | null>(null);

const key = "scarecrow.auth.token";

function getStoredToken(): string | null {
  return localStorage.getItem(key);
}

function setStoredToken(token: string | null) {
  if (token) {
    localStorage.setItem(key, token);
  } else {
    localStorage.removeItem(key);
  }
}

export function AuthProvider({ children }: PropsWithChildren<{}>) {
  const [token, setToken] = useState<string | null>(getStoredToken());
  const isAuthenticated = !!token;

  const logout = useCallback(async () => {
    setStoredToken(null);
    setToken(null);
  }, []);

  const login = useCallback(async (username: string) => {
    setStoredToken(username);
    setToken(username);
  }, []);

  useEffect(() => {
    setToken(getStoredToken());
  }, []);

  return (
    <AuthContext.Provider value={{ isAuthenticated, token, login, logout }}>
      {children}
    </AuthContext.Provider>
  );
}

export function useAuth() {
  const context = useContext(AuthContext);
  if (!context) {
    throw new Error("useAuth must be used within an AuthProvider");
  }
  return context;
}
