import { createFileRoute, useRouter } from "@tanstack/react-router";
import { useAuth } from "../AuthProvider";
import { useEffect } from "react";
import { useNavigate } from "@tanstack/react-router";

type VerifyParams = {
  code: string;
  state: string;
};

export const Route = createFileRoute("/verify")({
  validateSearch: (search: Record<string, unknown>): VerifyParams => {
    return {
      code: (search.code as string) || "",
      state: (search.state as string) || "",
    };
  },
  component: RouteComponent,
});

function RouteComponent() {
  const { code, state } = Route.useSearch();
  const auth = useAuth();
  const router = useRouter();
  const navigate = useNavigate();

  useEffect(() => {
    const doHandshake = async () => {
      if (state !== localStorage.getItem("latestCSRFToken")) {
        return;
      }
      const baseUrl = "https://oauth-proxy.sgt-pl.com";
      const params = [
        "url=https://github.com/login/oauth/access_token",
        "proj=scarecrow",
        `code=${code}`,
      ];
      const authResult = await fetch(`${baseUrl}?${params.join("&")}`).then(
        (res) => res.json(),
      );

      if ("access_token" in authResult) {
        auth.login(authResult["access_token"]);

        await router.invalidate();
        await navigate({ to: "/" });
      }
    };

    doHandshake();
  }, []);

  return <div>Logging in...</div>;
}
