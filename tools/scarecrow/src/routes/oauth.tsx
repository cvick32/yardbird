import { redirect } from "@tanstack/react-router";
import { createFileRoute } from "@tanstack/react-router";

export const Route = createFileRoute("/oauth")({
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      // the client id from github
      const client_id = "Ov23liTypAbgOxBn0ojH";

      // create a CSRF token and store it locally
      const state = Array.from(crypto.getRandomValues(new Uint8Array(16)))
        .map((b) => b.toString(16).padStart(2, "0"))
        .join("");
      localStorage.setItem("latestCSRFToken", state);

      const parts = [
        `client_id=${client_id}`,
        "response_type=code",
        "scope=repo",
        `redirect_url=${window.location.origin}/verify`,
        `state=${state}`,
      ];

      const link = `https://github.com/login/oauth/authorize?${parts.join("&")}`;
      window.location.href = link;
    } else {
      throw redirect({ to: "/" });
    }
  },
});
